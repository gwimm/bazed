#![allow(unused)]

use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use maplit::{hashmap, hashset};
use uuid::Uuid;

use crate::input_pattern::{Combo, InputPattern, Repetition};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
struct State(Uuid);
impl State {
    fn new() -> Self {
        State(Uuid::new_v4())
    }
}

type EdgeMap = HashMap<State, HashMap<Combo, State>>;

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
                    epsilon_edges.insert(start, hashset![nfa.start]);
                    epsilon_edges.insert(nfa.accept, hashset![accept]);
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
                    epsilon_edges.insert(start, hashset![nfa.start]);
                    epsilon_edges.insert(nfa.accept, hashset![accept]);
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
                    epsilon_edges.insert(last, hashset![nfa.start]);
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
                        .insert(nfa.accept, hashset![nfa.start]);
                    opt_nfa
                },
                Repetition::OneOrMore => {
                    let nfa = Nfa::from_input_pattern(*pat);
                    let mut opt_nfa = nfa.clone();
                    opt_nfa
                        .epsilon_edges
                        .insert(nfa.accept, hashset![nfa.start]);
                    opt_nfa
                },
            },
        }
    }

    pub(crate) fn minimize(&mut self) {
        while self.minimize_step() {}
    }

    pub(crate) fn minimize_step(&mut self) -> bool {
        let mut remove = Vec::new();
        for state_0 in &self.states {
            if remove.contains(state_0) {
                continue;
            }
            let edges_0 = self.edges.get(&state_0).cloned();
            let epsilons_0 = self.epsilon_edges.get(&state_0).cloned();
            for state_1 in &self.states {
                if remove.contains(state_1) {
                    continue;
                }
                let edges_1 = self.edges.get(&state_1);
                let epsilons_1 = self.epsilon_edges.get(&state_1);
                if edges_0.as_ref() == edges_1
                    && epsilons_0.as_ref() == epsilons_1
                    && state_0 != state_1
                {
                    remove.push(*state_1);
                    for e in self.edges.iter_mut() {
                        if remove.contains(e.0) {
                            continue;
                        }
                        for trans in e.1.iter_mut() {
                            if trans.1 == state_1 {
                                *trans.1 = *state_0;
                            }
                        }
                    }
                    for e in self.epsilon_edges.iter_mut() {
                        if remove.contains(e.0) {
                            continue;
                        }
                        if e.1.remove(state_1) {
                            e.1.insert(*state_0);
                        }
                    }
                }
            }
        }
        let did_change = !remove.is_empty();
        for s in remove {
            self.states.remove(&s);
            self.edges.remove(&s);
            self.epsilon_edges.remove(&s);
        }
        did_change
    }

    pub(crate) fn to_graphviz(&self) -> String {
        let a = self
            .edges
            .iter()
            .flat_map(|(a, paths)| {
                paths.iter().map(move |(trans, b)| {
                    format!(
                        "\"{a:?}\" -> \"{b:?}\" [label=\"{}\"];\n\"{a:?}\"[label=\"lmao\"];\n\"{b:?}\"[label=\"lmao\"];",
                        format!("{trans:?}").replace('"', "\'")
                    )
                })
            })
            .join("\n");
        let b = self
            .epsilon_edges
            .iter()
            .map(|(a, b)| format!("\"{a:?}\" -> \"{b:?}\" [label=\"ε\"];\n\"{a:?}\"[label=\"lmao\"];\n\"{b:?}\"[label=\"lmao\"];"))
            .join("\n");

        let colorized = format!(
            "\"{:?}\" [label=\"start\", color=\"green\"];\n\"{:?}\" [label=\"accept\", color=\"red\"]",
            self.start, self.accept
        );

        format!("digraph G {{\n{a}\n{b}\n{colorized}\n}}")
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
    //TODO clone lmao
    epsilon_edges.extend(nfa.epsilon_edges.clone());
    epsilon_edges.insert(nfa.accept, hashset![accept]);
    //TODO clone lmao
    edges.extend(nfa.edges.clone());
    Nfa {
        start,
        states,
        accept,
        epsilon_edges,
        edges,
    }
}
