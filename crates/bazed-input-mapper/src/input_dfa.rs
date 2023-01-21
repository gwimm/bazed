use std::{
    collections::{BTreeSet, HashMap, HashSet},
    convert::identity,
    sync::{atomic::AtomicUsize, LazyLock},
};

use itertools::Itertools;
use maplit::hashset;

use crate::{
    input_event::KeyInput,
    input_pattern::{Combo, InputPattern, Repetition},
};

#[derive(Clone, Copy, Eq, PartialEq, Hash, derive_more::Display, PartialOrd, Ord)]
struct State(usize);

impl std::fmt::Debug for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl State {
    fn new() -> Self {
        static COUNTER: LazyLock<AtomicUsize> = LazyLock::new(|| AtomicUsize::new(0));
        //State(Uuid::new_v4())
        State(COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst))
    }
}
//TODO clone lmao
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Nfa {
    start: State,
    states: HashSet<State>,
    edges: HashMap<State, HashMap<Combo, HashSet<State>>>,
    accept: HashSet<State>,

    capture_starts: HashMap<State, String>,
    capture_ends: HashMap<State, String>,
}

impl Nfa {
    fn new(start: State) -> Self {
        Self {
            start,
            accept: hashset![],
            states: hashset![start],
            edges: HashMap::new(),
            capture_starts: HashMap::new(),
            capture_ends: HashMap::new(),
        }
    }

    fn insert_edge(&mut self, from: State, combo: Combo, to: State) {
        self.edges
            .entry(from)
            .or_default()
            .entry(combo)
            .or_default()
            .insert(to);
    }

    fn has_edge(&self, s: &State, combo: &Combo, s2: &State) -> bool {
        self.edges
            .get(s)
            .map_or(false, |x| x.get(combo).map_or(false, |x| x.contains(s2)))
    }

    fn remove_state(&mut self, s: State) {
        assert!(self.start != s);
        self.states.remove(&s);
        self.edges.remove(&s);
        for edges in self.edges.values_mut() {
            for targets in edges.values_mut() {
                targets.remove(&s);
            }
        }
        self.accept.remove(&s);
    }

    pub(crate) fn remove_dead_ends(&mut self) {
        let mut remove = Vec::new();
        for s in &self.states {
            if self.accept.contains(s) {
                continue;
            }
            if self.edges.get(s).map_or(true, |x| x.is_empty()) {
                remove.push(*s);
            }
        }
        for s in remove {
            self.remove_state(s);
        }
    }

    pub(crate) fn simplify(&mut self) {
        loop {
            let mut identical = Vec::new();
            for s1 in &self.states {
                for s2 in &self.states {
                    if s1 == s2 {
                        continue;
                    }
                    if self.edges.get(s1) == self.edges.get(s2)
                        && self.start != *s1
                        && (self.accept.contains(s1) == self.accept.contains(s2))
                    {
                        identical.push((*s1, *s2));
                    }
                }
            }
            if identical.is_empty() {
                return;
            } else {
                println!("unifying {identical:?}");
            }

            for (a, b) in identical {
                if self.states.contains(&a) {
                    for edges in self.edges.values_mut() {
                        for targets in edges.values_mut() {
                            if targets.remove(&b) {
                                targets.insert(a);
                            }
                        }
                    }
                    self.remove_state(b);
                }
            }
        }
    }

    pub(crate) fn to_graphviz(&self) -> String {
        let a = self
            .edges
            .iter()
            .flat_map(|(a, paths)| paths.iter().map(move |(trans, b)| (a, trans, b)))
            .flat_map(|(a, trans, b)| b.iter().map(move |b| (a, trans, b)))
            .map(move |(a, trans, b)| edge_to_graphviz(a, trans, b))
            .join("\n");
        let start = format!(r#""{}" [label="start", color="green"];"#, self.start);
        let end = self
            .accept
            .iter()
            .map(|x| format!(r#""{x}" [label="accept", color="red"];"#))
            .join("\n");

        format!("digraph G {{\nrankdir = TB; node [shape = circle]; edge [weight = 2]; node [width = 0.3]; \n{a}\n{start}\n{end}\n}}")
    }
}

//TODO clone lmao
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct ENfa {
    start: State,
    states: HashSet<State>,
    edges: HashMap<State, HashMap<Combo, HashSet<State>>>,
    epsilons: HashMap<State, HashSet<State>>,
    accept: State,

    capture_starts: HashMap<State, String>,
    capture_ends: HashMap<State, String>,
}

impl ENfa {
    fn new(start: State, accept: State) -> Self {
        Self {
            start,
            accept,
            states: hashset![start, accept],
            edges: HashMap::new(),
            epsilons: HashMap::new(),
            capture_starts: HashMap::new(),
            capture_ends: HashMap::new(),
        }
    }

    fn into_optional(mut self) -> Self {
        self.insert_epsilon(self.start, self.accept);
        self
    }

    fn insert_epsilon(&mut self, from: State, to: State) {
        self.epsilons.entry(from).or_default().insert(to);
    }

    fn insert_edge(&mut self, from: State, combo: Combo, to: State) {
        self.edges
            .entry(from)
            .or_default()
            .entry(combo)
            .or_default()
            .insert(to);
    }

    fn at_edge(&self, s: &State, combo: &Combo) -> Option<&HashSet<State>> {
        self.edges.get(s).and_then(|x| x.get(combo))
    }

    fn edges_from(&self, s: &State) -> impl Iterator<Item = (&Combo, &State)> {
        self.edges
            .get(s)
            .into_iter()
            .flat_map(|x| x.iter())
            .flat_map(|(a, b)| b.iter().map(move |b| (a, b)))
    }

    fn epsilons_from(&self, s: &State) -> impl Iterator<Item = &State> {
        self.epsilons.get(s).into_iter().flat_map(|x| x.iter())
    }

    /// Extend this NFA by another NFA, adding its states, edges and epsilons.
    /// start and accepting states are unaffected
    fn extend(&mut self, other: ENfa) {
        self.states.extend(other.states);
        self.edges.extend(other.edges);
        self.epsilons.extend(other.epsilons);
        self.capture_starts.extend(other.capture_starts);
        self.capture_ends.extend(other.capture_ends);
    }

    pub(crate) fn from_input_pattern(pattern: InputPattern) -> ENfa {
        match pattern {
            InputPattern::Combo(combo) => {
                let mut nfa = Self::new(State::new(), State::new());
                nfa.insert_edge(nfa.start, combo, nfa.accept);
                nfa
            },
            InputPattern::Capture(name, pat) => {
                let mut nfa = ENfa::from_input_pattern(*pat);
                nfa.capture_starts.insert(nfa.start, name.to_string());
                nfa.capture_ends.insert(nfa.accept, name);
                nfa
            },
            InputPattern::Alternative(options) => {
                let mut new = ENfa::new(State::new(), State::new());
                for sub in options.into_iter().map(ENfa::from_input_pattern) {
                    new.insert_epsilon(new.start, sub.start);
                    new.insert_epsilon(sub.accept, new.accept);
                    new.extend(sub);
                }
                new
            },
            InputPattern::Sequence(seq) => {
                let start = State::new();
                // we start the nfa out with having the start state be accepting,
                // but then shift the accept state further to the end with every step of the seq
                let mut new = ENfa::new(start, start);
                for sub in seq.into_iter().map(ENfa::from_input_pattern) {
                    // Make the current end-state point to the sub-nfas start state
                    new.insert_epsilon(new.accept, sub.start);
                    // set the end of the sub-nfa to be the end of the seq-nfa
                    new.accept = sub.accept;
                    new.extend(sub);
                }
                new
            },
            InputPattern::Repeat(rep, pat) => match rep {
                Repetition::Optional => ENfa::from_input_pattern(*pat).into_optional(),
                Repetition::ZeroOrMore => {
                    let mut nfa = ENfa::from_input_pattern(*pat).into_optional();
                    nfa.insert_epsilon(nfa.accept, nfa.start);
                    nfa
                },
                Repetition::OneOrMore => {
                    let mut nfa = ENfa::from_input_pattern(*pat);
                    nfa.insert_epsilon(nfa.accept, nfa.start);
                    nfa
                },
            },
        }
    }

    pub(crate) fn test(&self, input: &[KeyInput]) -> bool {
        let mut todo = vec![(0, self.start, hashset![])];
        while let Some((i, state, mut epsilons_visited)) = todo.pop() {
            if state == self.accept {
                return true;
            }
            let symbol = input.get(i).cloned();
            if let Some(next) = symbol.and_then(|s| self.at_edge(&state, &Combo::from_input(s))) {
                for s in next {
                    todo.push((i + 1, *s, hashset![]));
                }
            } else if let Some(epsilon_reachable) = self.epsilons.get(&state) {
                let not_yet_visited: Vec<_> = epsilon_reachable
                    .difference(&epsilons_visited)
                    .copied()
                    .collect();
                for next_state in not_yet_visited.into_iter() {
                    epsilons_visited.insert(next_state);
                    todo.push((i, next_state, epsilons_visited.clone()));
                }
            } else {
                continue;
            }
        }
        false
    }

    pub(crate) fn remove_epsilons(self) -> Nfa {
        let mut nfa = Nfa::new(self.start);
        if self.accept == self.start {
            nfa.accept.insert(nfa.start);
        }

        let mut visited_eps: HashSet<(State, State)> = HashSet::new();
        let todo_epsilon = self
            .epsilons_from(&self.start)
            .map(|x| (self.start, None, *x));
        let mut todo: BTreeSet<_> = self
            .edges_from(&self.start)
            .map(|x| (self.start, Some(x.0), *x.1))
            .chain(todo_epsilon)
            .collect();

        while let Some((q1, via, q2)) = todo.pop_first() {
            if let Some(alpha) = via {
                nfa.states.insert(q2);
                nfa.insert_edge(q1, alpha.clone(), q2);
                if self.accept == q2 {
                    nfa.accept.insert(q2);
                }

                for q3 in self.epsilons_from(&q2) {
                    if !nfa.has_edge(&q1, alpha, q3) {
                        todo.insert((q1, Some(alpha), *q3));
                    }
                }
                for (via2, q3) in self.edges_from(&q2) {
                    if !nfa.has_edge(&q2, via2, q3) {
                        todo.insert((q2, Some(via2), *q3));
                    }
                }
            } else {
                visited_eps.insert((q1, q2));
                if self.accept == q2 {
                    nfa.accept.insert(q1);
                }

                for (via2, q3) in self.edges_from(&q2) {
                    if !nfa.has_edge(&q1, via2, q3) {
                        todo.insert((q1, Some(via2), *q3));
                    }
                }
                for q3 in self.epsilons_from(&q2) {
                    if !visited_eps.contains(&(q1, *q3)) {
                        todo.insert((q1, None, *q3));
                    }
                }
            }
        }
        nfa
    }

    fn reachable_between(&self, start: State, end: State) -> Vec<State> {
        let mut todo = vec![start];
        let mut visited = hashset![];
        let mut reachable = vec![];
        while let Some(next) = todo.pop() {
            reachable.push(next);
            if visited.contains(&next) {
                continue;
            }
            visited.insert(next);
            if next == end {
                continue;
            }
            todo.extend(self.edges_from(&next).map(|x| x.1));
            todo.extend(self.epsilons_from(&next));
        }
        reachable
    }

    pub(crate) fn to_graphviz(&self) -> String {
        let a = self
            .edges
            .iter()
            .flat_map(|(a, paths)| paths.iter().map(move |(trans, b)| (a, trans, b)))
            .flat_map(|(a, trans, b)| b.iter().map(move |b| (a, trans, b)))
            .map(move |(a, trans, b)| edge_to_graphviz(a, trans, b))
            .join("\n");
        let b = self
            .epsilons
            .iter()
            .flat_map(|(a, b)| b.iter().map(move |x| (a, x)))
            .map(|(a, b)| edge_to_graphviz(a, "ε", b))
            .join("\n");

        let colorized = format!(
            r#""{}" [label="start", color="green"]; "{}" [label="accept", color="red"]"#,
            self.start, self.accept
        );

        format!("digraph G {{\nrankdir = TB; node [shape = circle]; edge [weight = 2]; node [width = 0.3]; \n{a}\n{b}\n{colorized}\n}}")
    }
}

fn edge_to_graphviz(a: &State, edge: impl std::fmt::Display, b: &State) -> String {
    format!(
        "\"{a}\" -> \"{b}\" [label=\"{}\"];",
        format!("{edge}").replace('"', "\'")
    )
}
