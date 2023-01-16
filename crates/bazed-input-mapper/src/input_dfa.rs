#![allow(unused)]

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    sync::{atomic::AtomicUsize, LazyLock},
};

use itertools::Itertools;
use maplit::{hashmap, hashset};
use uuid::Uuid;

use crate::{
    input_event::KeyInput,
    input_pattern::{Combo, InputPattern, Repetition},
};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, derive_more::Display, PartialOrd, Ord)]
struct State(usize);

impl State {
    fn new() -> Self {
        static COUNTER: LazyLock<AtomicUsize> = LazyLock::new(|| AtomicUsize::new(0));
        //State(Uuid::new_v4())
        State(COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst))
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub(crate) struct Group {
    start: State,
    end: State,
    sub: HashMap<String, Group>,
}

impl Group {
    fn to_graphviz(&self, nfa: &Nfa, name: &str) -> String {
        format!(
            "subgraph cluster_{name}{} {{ label=\"{name}\"; {};\n{} }}",
            Uuid::new_v4().as_u128(),
            nfa.reachable_between(self.start, self.end)
                .iter()
                .join("\n"),
            self.sub
                .iter()
                .map(|(name, group)| group.to_graphviz(nfa, name))
                .join("\n")
        )
    }
}

//TODO clone lmao
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Nfa {
    start: State,
    states: HashSet<State>,
    edges: HashMap<State, HashMap<Combo, State>>,
    epsilons: HashMap<State, HashSet<State>>,
    accept: State,

    captures: HashMap<String, Group>,
}

impl Nfa {
    fn new(start: State, accept: State) -> Self {
        Self {
            start,
            accept,
            states: hashset![start, accept],
            edges: HashMap::new(),
            epsilons: HashMap::new(),
            captures: HashMap::new(),
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
        self.edges.entry(from).or_default().insert(combo, to);
    }

    /// Extend this NFA by another NFA, adding its states, edges and epsilons.
    /// start and accepting states are unaffected
    fn extend(&mut self, other: Nfa) {
        self.states.extend(other.states);
        self.edges.extend(other.edges);
        self.epsilons.extend(other.epsilons);
        self.captures.extend(other.captures);
    }

    pub(crate) fn from_input_pattern(pattern: InputPattern) -> Nfa {
        match pattern {
            InputPattern::Combo(combo) => {
                let mut nfa = Self::new(State::new(), State::new());
                nfa.insert_edge(nfa.start, combo, nfa.accept);
                nfa
            },
            InputPattern::Capture(name, pat) => {
                let mut nfa = Nfa::from_input_pattern(*pat);
                let group = Group {
                    start: nfa.start,
                    end: nfa.accept,
                    sub: nfa.captures,
                };
                nfa.captures = hashmap! { name => group };
                nfa
            },
            InputPattern::Alternative(options) => {
                let mut new = Nfa::new(State::new(), State::new());
                for sub in options.into_iter().map(Nfa::from_input_pattern) {
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
                let mut new = Nfa::new(start, start);
                for sub in seq.into_iter().map(Nfa::from_input_pattern) {
                    // Make the current end-state point to the sub-nfas start state
                    new.insert_epsilon(new.accept, sub.start);
                    // set the end of the sub-nfa to be the end of the seq-nfa
                    new.accept = sub.accept;
                    new.extend(sub);
                }
                new
            },
            InputPattern::Repeat(rep, pat) => match rep {
                Repetition::Optional => Nfa::from_input_pattern(*pat).into_optional(),
                Repetition::ZeroOrMore => {
                    let mut nfa = Nfa::from_input_pattern(*pat).into_optional();
                    nfa.insert_epsilon(nfa.accept, nfa.start);
                    nfa
                },
                Repetition::OneOrMore => {
                    let mut nfa = Nfa::from_input_pattern(*pat);
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
            let edges = self.edges.get(&state);
            if let Some(next_state) =
                symbol.and_then(|s| edges.and_then(|e| e.get(&Combo::from_input(s))))
            {
                todo.push((i + 1, *next_state, hashset![]));
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

    pub(crate) fn simplify(&mut self) {
        // list of tuples (<state that should be removed>, <state that should replace it>)
        let mut remove = Vec::new();
        for state in &self.states {
            if self.edges.get(state).map_or(false, |x| !x.is_empty()) {
                continue;
            }
            let Some(epsilons) = self.epsilons.get(state) else { continue };
            if epsilons.len() == 1 {
                remove.push((*state, *epsilons.iter().next().unwrap()));
            }
        }
        for (state, new_target) in &remove {
            for mut edge in self.edges.values_mut() {
                for target in edge.values_mut().filter(|target| *target == state) {
                    *target = *new_target;
                }
            }
            for mut epsilons in self.epsilons.values_mut() {
                if epsilons.remove(state) {
                    epsilons.insert(*new_target);
                }
            }
        }
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
            if let Some(edges) = self.edges.get(&next) {
                todo.extend(edges.values());
            }
            if let Some(epsilons) = self.epsilons.get(&next) {
                todo.extend(epsilons);
            }
        }
        reachable
    }

    pub(crate) fn to_graphviz(&self) -> String {
        let a = self
            .edges
            .iter()
            .flat_map(|(a, paths)| paths.iter().map(move |(trans, b)| (a, trans, b)))
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
        let subgraphs = self
            .captures
            .iter()
            .map(|(name, group)| group.to_graphviz(self, name))
            .join("\n");

        format!("digraph G {{\nrankdir = TB; node [shape = circle]; edge [weight = 2]; node [width = 0.3]; \n{a}\n{b}\n{colorized}\n{subgraphs}\n}}")
    }
}

fn edge_to_graphviz(a: &State, edge: impl std::fmt::Display, b: &State) -> String {
    format!(
        "\"{a}\" -> \"{b}\" [label=\"{}\"];",
        format!("{edge}").replace('"', "\'")
    )
}
