use std::{
    collections::{BTreeSet, HashMap, HashSet},
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

    capture_starts: HashMap<State, Vec<String>>,
    capture_ends: HashMap<State, Vec<String>>,
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

    fn at_edge(&self, s: &State, combo: &Combo) -> Option<&HashSet<State>> {
        self.edges.get(s).and_then(|x| x.get(combo))
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

    pub(crate) fn test(&self, input: &[KeyInput]) -> bool {
        let mut todo = vec![(0, self.start)];
        while let Some((i, state)) = todo.pop() {
            if self.accept.contains(&state) {
                return true;
            }
            let Some(sym) = input.get(i) else { return false };
            let next = self.at_edge(&state, &Combo::from_input(sym.clone()));
            let next = next.iter().flat_map(|x| x.iter());
            for s in next {
                todo.push((i + 1, *s));
            }
        }
        false
    }

    pub(crate) fn get_groups<'a>(
        &self,
        input: &'a [KeyInput],
    ) -> Option<HashMap<String, &'a [KeyInput]>> {
        println!("starts: {:?}", self.capture_starts);
        println!("ends: {:?}", self.capture_ends);
        let mut todo = vec![(
            0,
            self.start,
            HashMap::new(),
            HashMap::<String, (usize, usize)>::new(),
        )];
        while let Some((i, state, mut completed_groups, mut active_groups)) = todo.pop() {
            for started in self
                .capture_starts
                .get(&state)
                .iter()
                .flat_map(|x| x.iter())
            {
                active_groups.insert(started.clone(), (i, i));
            }

            for ended in self.capture_ends.get(&state).iter().flat_map(|x| x.iter()) {
                if let Some((ended, captured)) = active_groups.remove_entry(ended) {
                    completed_groups.insert(ended, &input[captured.0..captured.1 + 1]);
                } else {
                    println!("fucked: {ended:?}");
                }
            }

            if self.accept.contains(&state) {
                return Some(completed_groups);
            }
            let Some(sym) = input.get(i) else { return None };

            for (_, ref mut captured) in active_groups.iter_mut() {
                captured.1 = i;
            }

            let next = self.at_edge(&state, &Combo::from_input(sym.clone()));
            let next = next.iter().flat_map(|x| x.iter());
            for s in next {
                todo.push((i + 1, *s, completed_groups.clone(), active_groups.clone()));
            }
        }
        None
    }

    pub(crate) fn remove_dead_ends(&mut self) {
        let mut remove = Vec::new();
        for s in &self.states {
            if !self.accept.contains(s) && self.edges.get(s).map_or(true, |x| x.is_empty()) {
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

            for (a, b) in self.states.iter().cartesian_product(self.states.iter()) {
                if a != b
                    && self.edges.get(a) == self.edges.get(b)
                    && self.start != *a
                    && (self.accept.contains(a) == self.accept.contains(b))
                {
                    identical.push((*a, *b));
                }
            }
            if identical.is_empty() {
                return;
            }
            for (a, b) in identical {
                if self.states.contains(&a) {
                    for targets in self.edges.values_mut().flat_map(|x| x.values_mut()) {
                        if targets.remove(&b) {
                            targets.insert(a);
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
        let start = format!(r#""start" -> "{}"; "start" [style=invis]; "#, self.start);
        let end = self
            .accept
            .iter()
            .map(|x| format!(r#""{x}" [shape=doublecircle, color="red"];"#))
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

    pub(crate) fn remove_epsilons(mut self) -> Nfa {
        let mut nfa = Nfa::new(self.start);
        if self.accept == self.start {
            nfa.accept.insert(nfa.start);
        }

        // mappings from old nfa to new nfa
        let mut mappings = HashMap::new();

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
                mappings.insert(q2, q2);

                nfa.insert_edge(q1, alpha.clone(), q2);
                if self.accept == q2 {
                    nfa.accept.insert(q2);
                }

                for q3 in self.epsilons_from(&q2) {
                    if !nfa.has_edge(&q1, alpha, q3) {
                        mappings.insert(q2, *q3);
                        todo.insert((q1, Some(alpha), *q3));
                    }
                }
                for (via2, q3) in self.edges_from(&q2) {
                    if !nfa.has_edge(&q2, via2, q3) {
                        mappings.insert(q2, *q3);
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
                        mappings.insert(q2, *q3);
                        todo.insert((q1, Some(via2), *q3));
                    }
                }
                for q3 in self.epsilons_from(&q2) {
                    if !visited_eps.contains(&(q1, *q3)) {
                        mappings.insert(q2, *q3);
                        todo.insert((q1, None, *q3));
                    }
                }
            }
        }

        println!("{mappings:?}");

        for (state, name) in self.capture_starts.drain() {
            if let Some(s) = mappings.get(&state) {
                let mut s = s;
                while let Some(mapped) = mappings.get(s) {
                    if mapped == s {
                        break;
                    }
                    s = mapped;
                }
                nfa.capture_starts.entry(*s).or_default().push(name);
            }
        }
        for (state, name) in self.capture_ends.drain() {
            if let Some(s) = mappings.get(&state) {
                let mut s = s;
                while let Some(mapped) = mappings.get(s) {
                    if mapped == s {
                        break;
                    }
                    s = mapped;
                }
                nfa.capture_ends.entry(*s).or_default().push(name);
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

        let start = format!(r#""start" -> "{}"; "start" [style=invis]; "#, self.start);
        let end = format!(r#""{}" [shape=doublecircle, color="red"];"#, self.accept);

        format!("digraph G {{\nrankdir = TB; node [shape = circle]; edge [weight = 2]; node [width = 0.3]; \n{a}\n{b}\n{start}\n{end}\n}}")
    }
}

fn edge_to_graphviz(a: &State, edge: impl std::fmt::Display, b: &State) -> String {
    format!(
        "\"{a}\" -> \"{b}\" [label=\"{}\"];",
        format!("{edge}").replace('"', "\'")
    )
}
