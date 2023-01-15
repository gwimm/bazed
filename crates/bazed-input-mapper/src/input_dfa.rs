#![allow(unused)]

use std::{
    collections::{HashMap, HashSet},
    sync::{atomic::AtomicUsize, LazyLock},
};

use itertools::Itertools;
use maplit::{hashmap, hashset};
use uuid::Uuid;

use crate::input_pattern::{Combo, InputPattern, Repetition};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, derive_more::Display)]
struct State(usize);

impl State {
    fn new() -> Self {
        static COUNTER: LazyLock<AtomicUsize> = LazyLock::new(|| AtomicUsize::new(0));
        //State(Uuid::new_v4())
        State(COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst))
    }
}

type EdgeMap = HashMap<State, HashMap<Combo, State>>;

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Dfa {
    start: State,
    states: HashSet<State>,
    edges: EdgeMap,
    accepting: HashSet<State>,
}

//TODO clone lmao
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Nfa {
    start: State,
    states: HashSet<State>,
    edges: EdgeMap,
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

    fn reachable_by_epsilon(&self, start: State) -> HashSet<State> {
        let mut reached: HashSet<State> = HashSet::new();
        let mut todo = Vec::new();
        reached.insert(start);
        todo.push(start);
        while let Some(next) = todo.pop() {
            let Some(reachable) = self.epsilons.get(&next) else { continue };
            for state in reachable {
                if reached.insert(*state) {
                    todo.push(*state)
                }
            }
        }
        reached
    }

    pub(crate) fn into_dfa(self) -> Dfa {
        // https://www.educative.io/answers/how-to-convert-nfa-to-dfa
        // https://docs.rs/automata/0.0.4/automata/nfa/struct.Nfa.html#method.to_regex

        let start_closure = self.reachable_by_epsilon(self.start);
        let dfa_start_state = State::new();
        // map of DFA state to the NFA states it represents
        let mut state_sets = hashmap! {dfa_start_state => start_closure};
        let mut dfa_edges: HashMap<State, HashMap<Combo, State>> = HashMap::new();
        let mut todo = vec![dfa_start_state];
        let mut accepting = HashSet::new();

        while let Some(next_dfa) = todo.pop() {
            // set of all states that this closure represents
            let nfa_state_set = state_sets.get(&next_dfa).unwrap();

            // map of edges from nfa-states corresponding to this dfa state _directly_ to other NFA states.
            let mut outgoing: HashMap<Combo, HashSet<State>> = HashMap::new();

            // fill the outgoing-edges hashmap
            // for every nfa-state represented by the current dfa state
            for nfa_state in nfa_state_set.clone() {
                // get the edges and combine ones that have the same combo into states.
                let Some(nfa_edges) = self.edges.get(&nfa_state) else { continue };
                for (combo, nfa_target) in nfa_edges {
                    outgoing
                        .entry(combo.clone())
                        .or_default()
                        .insert(*nfa_target);
                }
            }

            for (combo, direct_nfa_targets) in outgoing {
                // calculate epsilon closures of all these nfa-target states
                let mut closure: HashSet<State> = direct_nfa_targets
                    .iter()
                    .flat_map(|x| self.reachable_by_epsilon(*x).into_iter())
                    .collect();
                closure.extend(direct_nfa_targets);

                // The dfa state that represents the set of these nfa states.
                // TODO this is currently horribly inefficient. Lookup by the closure is garbo
                let closure_dfa_state = state_sets
                    .iter()
                    .find(|(_, v)| closure == **v)
                    .map(|x| *x.0)
                    .unwrap_or_else(|| {
                        let s = State::new();
                        state_sets.insert(s, closure.clone());
                        todo.push(s);
                        s
                    });
                if closure.contains(&self.accept) {
                    accepting.insert(closure_dfa_state);
                }

                dfa_edges
                    .entry(next_dfa)
                    .or_default()
                    .insert(combo, closure_dfa_state);
            }
        }

        let x = Dfa {
            start: dfa_start_state,
            accepting,
            edges: dfa_edges,
            states: state_sets.keys().cloned().collect(),
        };

        println!(
            "{} {}}}",
            x.to_graphviz().trim_end_matches('}'),
            state_sets
                .iter()
                .map(|(k, v)| format!("\"{k}\" [label=\"{}\"]", v.iter().join(",")))
                .join(";\n")
        );
        x
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

impl Dfa {
    pub(crate) fn to_graphviz(&self) -> String {
        let a = self
            .edges
            .iter()
            .flat_map(|(a, paths)| paths.iter().map(move |(trans, b)| (a, trans, b)))
            .map(move |(a, trans, b)| edge_to_graphviz(a, trans, b))
            .join("\n");

        let colorized = format!(
            "\"{}\" [color=\"yellow\"];\n{}",
            self.start,
            self.accepting
                .iter()
                .map(|x| format!("\"{x}\" [color=\"green\"]"))
                .join(";"),
        );

        format!("digraph G {{\nrankdir = TB; node [shape = circle]; edge [weight = 2]; node [width = 0.3]; \n{a}\n{colorized}\n}}")
    }
}

fn edge_to_graphviz(a: &State, edge: impl std::fmt::Display, b: &State) -> String {
    format!(
        "\"{a}\" -> \"{b}\" [label=\"{}\"];",
        format!("{edge}").replace('"', "\'")
    )
}
