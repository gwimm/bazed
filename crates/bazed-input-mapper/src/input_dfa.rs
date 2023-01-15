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
    epsilon_edges: HashMap<State, HashSet<State>>,
    accept: State,
}

impl Nfa {
    pub(crate) fn from_input_pattern(pattern: InputPattern) -> Nfa {
        match pattern {
            InputPattern::Combo(combo) => {
                let start = State::new();
                let accept = State::new();
                Self {
                    start,
                    states: hashset![start, accept],
                    accept,
                    edges: hashmap! { start => hashmap! { combo => accept } },
                    epsilon_edges: HashMap::new(),
                }
            },
            InputPattern::Alternative(options) => {
                // TODO capture groups here!!!!
                let start = State::new();
                let accept = State::new();
                let mut states = HashSet::new();
                let mut epsilon_edges = HashMap::new();
                let mut edges = HashMap::new();
                for nfa in options.into_iter().map(|(_, x)| Nfa::from_input_pattern(x)) {
                    states.extend(nfa.states);
                    edges.extend(nfa.edges);
                    epsilon_edges.extend(nfa.epsilon_edges);
                    epsilon_edges.entry(start).or_default().insert(nfa.start);
                    epsilon_edges.entry(nfa.accept).or_default().insert(accept);
                }
                Nfa {
                    start,
                    states,
                    accept,
                    epsilon_edges,
                    edges,
                }
            },
            InputPattern::OneOf(options) => {
                let start = State::new();
                let accept = State::new();
                let mut states = HashSet::new();
                let mut epsilon_edges = HashMap::new();
                let mut edges = HashMap::new();
                for nfa in options.into_iter().map(Nfa::from_input_pattern) {
                    states.extend(nfa.states);
                    edges.extend(nfa.edges);
                    epsilon_edges.extend(nfa.epsilon_edges);
                    epsilon_edges.entry(start).or_default().insert(nfa.start);
                    epsilon_edges.entry(nfa.accept).or_default().insert(accept);
                }
                Nfa {
                    start,
                    states,
                    accept,
                    epsilon_edges,
                    edges,
                }
            },
            InputPattern::Sequence(seq) => {
                // TODO capture groups here!!!!
                let start = State::new();
                let mut accept = State::new();
                let mut states = HashSet::new();
                let mut epsilon_edges = HashMap::new();
                let mut edges = HashMap::new();
                let mut last = start;
                for nfa in seq.into_iter().map(|(_, x)| Nfa::from_input_pattern(x)) {
                    states.extend(nfa.states);
                    edges.extend(nfa.edges);
                    epsilon_edges.extend(nfa.epsilon_edges);
                    epsilon_edges.entry(last).or_default().insert(nfa.start);
                    last = nfa.accept;
                    accept = nfa.accept;
                }
                Nfa {
                    start,
                    states,
                    accept,
                    epsilon_edges,
                    edges,
                }
            },
            InputPattern::Repeat(rep, pat) => match rep {
                Repetition::Optional => rep_optional_nfa(Nfa::from_input_pattern(*pat)),
                Repetition::ZeroOrMore => {
                    let nfa = Nfa::from_input_pattern(*pat);
                    let mut opt_nfa = rep_optional_nfa(nfa.clone());
                    opt_nfa
                        .epsilon_edges
                        .entry(nfa.accept)
                        .or_default()
                        .insert(nfa.start);
                    opt_nfa
                },
                Repetition::OneOrMore => {
                    let nfa = Nfa::from_input_pattern(*pat);
                    let mut opt_nfa = nfa.clone();
                    opt_nfa
                        .epsilon_edges
                        .entry(nfa.accept)
                        .or_default()
                        .insert(nfa.start);
                    opt_nfa
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
            let Some(reachable) = self.epsilon_edges.get(&next) else { continue };
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
                .join(";")
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
            .epsilon_edges
            .iter()
            .flat_map(|(a, b)| b.iter().map(move |x| (a, x)))
            .map(|(a, b)| edge_to_graphviz(a, "ε", b))
            .join("\n");

        let colorized = format!(
            r#""{}" [label="start", color="green"];\n"{}" [label="accept", color="red"]"#,
            self.start, self.accept
        );

        format!("digraph G {{\nrankdir = TB; node [shape = circle]; edge [weight = 2]; node [width = 0.3]; \n{a}\n{b}\n{colorized}\n}}")
    }
}

fn rep_optional_nfa(nfa: Nfa) -> (Nfa) {
    let start = State::new();
    let accept = State::new();
    let mut states = hashset![start, accept];
    let mut epsilon_edges = hashmap! {start => hashset![accept], start => hashset![nfa.start]};
    let mut edges = HashMap::new();
    //TODO clone lmao
    states.extend(nfa.states.clone());
    epsilon_edges.extend(nfa.epsilon_edges);
    epsilon_edges.entry(nfa.accept).or_default().insert(accept);
    edges.extend(nfa.edges);
    Nfa {
        start,
        states,
        accept,
        epsilon_edges,
        edges,
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
