#![allow(unused)]

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    sync::{atomic::AtomicUsize, LazyLock},
};

use itertools::Itertools;
use maplit::{hashmap, hashset};
use uuid::Uuid;

use crate::input_pattern::{Combo, InputPattern, Repetition};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, derive_more::Display, PartialOrd, Ord)]
struct State(usize);

impl State {
    fn new() -> Self {
        static COUNTER: LazyLock<AtomicUsize> = LazyLock::new(|| AtomicUsize::new(0));
        //State(Uuid::new_v4())
        State(COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst))
    }
}

//TODO clone lmao
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Nfa {
    start: State,
    states: HashSet<State>,
    edges: HashMap<State, HashMap<Combo, State>>,
    epsilons: HashMap<State, HashSet<State>>,
    accept: State,
}

impl Nfa {
    fn new(start: State, accept: State) -> Self {
        Self {
            start,
            accept,
            states: hashset![start, accept],
            edges: HashMap::new(),
            epsilons: HashMap::new(),
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
    }

    pub(crate) fn from_input_pattern(pattern: InputPattern) -> Nfa {
        match pattern {
            InputPattern::Combo(combo) => {
                let mut nfa = Self::new(State::new(), State::new());
                nfa.insert_edge(nfa.start, combo, nfa.accept);
                nfa
            },
            InputPattern::Capture(name, pat) => Nfa::from_input_pattern(*pat),
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

        format!("digraph G {{\nrankdir = TB; node [shape = circle]; edge [weight = 2]; node [width = 0.3]; \n{a}\n{b}\n{colorized}\n}}")
    }
}

fn edge_to_graphviz(a: &State, edge: impl std::fmt::Display, b: &State) -> String {
    format!(
        "\"{a}\" -> \"{b}\" [label=\"{}\"];",
        format!("{edge}").replace('"', "\'")
    )
}
