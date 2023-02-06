use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    ops::Range,
};

use crate::common::Id;

type State = Id;

#[derive(Clone)]
pub enum Regex<A> {
    Symbol(A),
    Tag,
    Alternative(Box<Regex<A>>, Box<Regex<A>>),
    Sequence(Box<Regex<A>>, Box<Regex<A>>),

    /// ?, 0, Some(1)
    /// +, 1, None
    /// *, 0, None
    Repetition(Box<Regex<A>>, usize, Option<usize>),
}

pub fn many<A>(rx: Regex<A>) -> Regex<A> {
    Regex::Repetition(Box::new(rx), 0, None)
}

pub fn many1<A>(rx: Regex<A>) -> Regex<A> {
    Regex::Repetition(Box::new(rx), 1, None)
}

pub fn alt<A>(lhs: Regex<A>, rhs: Regex<A>) -> Regex<A> {
    Regex::Alternative(Box::new(lhs), Box::new(rhs))
}

pub fn seq<A>(rx1: Regex<A>, rx2: Regex<A>) -> Regex<A> {
    Regex::Sequence(Box::new(rx1), Box::new(rx2))
}

#[cfg(test)]
mod regex_test {
    use super::{alt, many, many1, seq, Regex};

    pub(crate) fn digit() -> Regex<char> {
        let mut iter = ('0'..'9').into_iter().map(|c| Regex::Symbol(c));
        let init = iter.next().unwrap();
        iter.fold(init, |acc, sym| {
            Regex::Alternative(Box::new(acc), Box::new(sym))
        })
    }

    pub(crate) fn digit1() -> Regex<char> {
        let mut iter = ('1'..'9').into_iter().map(|c| Regex::Symbol(c));
        let init = iter.next().unwrap();
        iter.fold(init, |acc, sym| alt(acc, sym))
    }

    pub(crate) fn number() -> Regex<char> {
        seq(digit(), many(digit()))
    }

    pub(crate) fn re2c_paper() -> Regex<char> {
        let a = Regex::Symbol('a');
        let b = Regex::Symbol('b');
        let an = many(seq(Regex::Tag, seq(a.clone(), Regex::Tag)));
        let ab = alt(a, seq(b.clone(), Regex::Tag));
        let bn = seq(Regex::Tag, many(b));
        seq(an, seq(ab, bn))
    }

    pub(crate) fn wikipedia() -> Regex<char> {
        let t = Regex::Tag;
        let a = Regex::Symbol('a');
        let b = Regex::Symbol('b');
        alt(seq(many(a.clone()), seq(t, many(b.clone()))), seq(a, b))
    }
}

#[derive(Hash, Clone, PartialEq, Eq)]
enum Edge<A> {
    Step(A),
    Epsilon(Option<(bool, usize)>),
}

pub struct Tenfa<A: Hash + Eq> {
    start: State,
    accept: State,
    tag_count: usize,
    transitions: HashMap<State, HashMap<Edge<A>, HashSet<State>>>,
}

#[allow(dead_code)]
pub struct Configuration {
    state: State,
    registers: Vec<Register>,
}

type Register = Option<usize>;

#[derive(Clone)]
pub struct Simulation {
    offset: usize,
    configs: Vec<(State, Vec<Register>)>,
}

impl Simulation {
    pub fn new<A: Hash + Eq>(tenfa: Tenfa<A>) -> Self {
        let registers = (0..tenfa.tag_count).into_iter().map(|_| None).collect();
        Self {
            offset: 0,
            configs: Vec::from([(tenfa.start, registers)]),
        }
    }
}

impl<A: Hash + Eq> From<(State, A, State)> for Tenfa<A> {
    fn from((start, symbol, accept): (State, A, State)) -> Self {
        Self {
            start,
            accept,
            tag_count: 0,
            transitions: HashMap::from([(
                start,
                HashMap::from([(Edge::Step(symbol), HashSet::from([accept]))]),
            )]),
        }
    }
}

impl<A: Hash + Eq + Clone> From<Regex<A>> for Tenfa<A> {
    fn from(regex: Regex<A>) -> Self {
        let mut tenfa = Self::epsilon(State::gen());
        tenfa.regex_extend(regex);
        tenfa
    }
}

impl<A: Hash + Eq + Clone> Tenfa<A> {
    fn epsilon(accept: State) -> Self {
        Self {
            start: accept,
            accept,
            tag_count: 0,
            transitions: HashMap::new(),
        }
    }

    pub fn step(&self, simulation: Simulation, input: &A) -> Simulation {
        Simulation {
            offset: simulation.offset + 1,
            configs: simulation
                .configs
                .into_iter()
                .filter_map(|(src, rs)| {
                    self.step_from(&src, input)
                        .map(|dsts| dsts.into_iter().map(move |dst| (dst, rs.clone())))
                })
                .flatten()
                .map(move |(state, rs)| (state.clone(), rs))
                .collect::<Vec<(State, Vec<Register>)>>(),
        }
    }

    fn regex_extend(&mut self, rx: Regex<A>) {
        match rx {
            Regex::Tag => self.extend_tag(),
            Regex::Symbol(sym) => self.extend_step(sym),
            Regex::Sequence(lhs, rhs) => self.regex_extend_seq(*lhs, *rhs),
            Regex::Alternative(lhs, rhs) => self.regex_extend_alt(*lhs, *rhs),
            Regex::Repetition(rx, low, count) => self.regex_extend_rep(*rx, low, count),
        }
    }

    fn regex_extend_rep(&mut self, rx: Regex<A>, low: usize, count: Option<usize>) {
        match (low, count) {
            (0, Some(0)) => panic!("optional never"),
            (low @ 2.., count) => {
                self.regex_extend_rep(rx.clone(), low - 1, count);
                self.regex_extend(rx);
            },
            (1, Some(0)) => self.regex_extend(rx),
            (1, Some(count @ 1..)) => {
                // if m == 1 then ?
                let accept = self.start;
                self.regex_extend_rep(rx.clone(), 1, Some(count - 1));
                self.binary_epsilon_branch(accept, self.start);
                self.regex_extend(rx);
            },
            (0, m) => {
                let accept = self.start;
                let accept_tag_count = self.tag_count;

                self.regex_extend_rep(rx, 1, m);
                let rx_start = self.start;
                let rx_tag_count = self.tag_count;

                self.start = accept;
                self.negative_tags_extend(accept_tag_count..rx_tag_count);
                let ntags_start = self.start;

                self.binary_epsilon_branch(rx_start, ntags_start);
            },
            (1, None) => {
                // +
                self.extend_edge(Edge::Epsilon(None));
                let accept = self.start;
                self.regex_extend(rx);
                self.extend_transitions_once((accept, Edge::Epsilon(None), self.start));
            },
            _ => unreachable!(),
        }
    }

    fn regex_extend_seq(&mut self, lhs: Regex<A>, rhs: Regex<A>) {
        self.regex_extend(rhs);
        self.regex_extend(lhs);
    }

    fn regex_extend_alt(&mut self, lhs: Regex<A>, rhs: Regex<A>) {
        let accept = self.start;
        let accept_tag_count = self.tag_count;

        self.regex_extend(lhs);
        let lhs_start = self.start;
        let lhs1_tag_count = self.tag_count;

        self.start = accept;
        self.negative_tags_extend(accept_tag_count..lhs1_tag_count);
        self.regex_extend(rhs);
        let rhs_start = self.start;
        let lhs2_tag_count = self.tag_count;

        self.start = lhs_start;
        self.negative_tags_extend(lhs1_tag_count..lhs2_tag_count);

        self.binary_epsilon_branch(rhs_start, self.start);
    }

    fn extend_step(&mut self, sym: A) {
        self.extend_edge(Edge::Step(sym));
    }

    fn extend_tag(&mut self) {
        self.extend_edge(Edge::Epsilon(Some((true, self.tag_count))));
        self.tag_count += 1;
    }

    fn extend_edge(&mut self, edge: Edge<A>) {
        let start = State::gen();
        self.extend_transitions_once((start, edge, self.start));
        self.start = start;
    }

    fn extend_transitions<I>(&mut self, other: I)
    where
        I: IntoIterator<Item = (State, HashMap<Edge<A>, HashSet<State>>)>,
    {
        for (src, steps) in other {
            let transitions = self.transitions.entry(src).or_default();
            for (edge, dsts) in steps {
                transitions.entry(edge).or_default().extend(dsts);
            }
        }
    }

    fn extend_transitions_once(&mut self, (src, edge, dst): (State, Edge<A>, State)) {
        self.transitions
            .entry(src)
            .or_default()
            .entry(edge)
            .or_default()
            .insert(dst);
    }

    fn binary_epsilon_branch(&mut self, lhs: State, rhs: State) {
        self.start = State::gen();
        self.extend_transitions_once((self.start, Edge::Epsilon(None), rhs));
        self.extend_transitions_once((self.start, Edge::Epsilon(None), lhs));
    }

    fn negative_tags_extend(&mut self, tag_range: Range<usize>) {
        for tag in tag_range {
            self.extend_edge(Edge::Epsilon(Some((false, tag))))
        }
    }

    pub fn epsilon_closure(&self, simulation: Simulation) -> Simulation {
        let mut stack = simulation.configs;
        stack.reverse();

        let mut configs = Vec::new();

        while let Some((src, mut rs)) = stack.pop() {
            configs.push((src, rs.clone()));

            let epsilons = self
                .iter_epsilons_from(&src)
                .flat_map(|(tag, dsts)| dsts.into_iter().map(move |dst| (tag, dst)));

            for (tag, dst) in epsilons {
                match tag {
                    Some((true, tag)) => rs[tag as usize] = Some(simulation.offset),
                    Some((false, tag)) => rs[tag as usize] = None,
                    _ => {},
                }

                if configs.iter().all(|(state, _)| state != dst) {
                    stack.push((*dst, rs.clone()))
                }
            }
        }

        // only retain determined steps and final states
        configs.retain(|(state, _)| !self.steps_from(state).is_empty() || state == &self.accept);

        Simulation {
            offset: simulation.offset,
            configs,
        }
    }

    fn step_from(&self, state: &State, symbol: &A) -> Option<&HashSet<State>> {
        self.steps_from(state).get(symbol).copied()
    }

    fn steps_from(&self, state: &State) -> HashMap<&A, &HashSet<State>> {
        self.transitions
            .get(state)
            .into_iter()
            .flatten()
            .filter_map(|(edge, dsts)| {
                if let Edge::Step(symbol) = edge {
                    Some((symbol, dsts))
                } else {
                    None
                }
            })
            .collect()
    }

    fn iter_epsilons_from(
        &self,
        state: &State,
    ) -> impl Iterator<Item = (Option<(bool, usize)>, &HashSet<State>)> {
        self.transitions
            .get(state)
            .into_iter()
            .flatten()
            .filter_map(|(edge, dsts)| {
                if let Edge::Epsilon(tag) = edge {
                    Some((tag.as_ref().copied(), dsts))
                } else {
                    None
                }
            })
    }
}

#[cfg(test)]
mod test {
    use std::{fmt::Display, hash::Hash};

    use super::regex_test as regex;
    use super::Tenfa;

    #[test]
    fn number() {
        let tenfa = regex::number().into();
        print_tenfa(&tenfa);
    }

    #[test]
    fn re2c_paper() {
        let tenfa = regex::re2c_paper().into();
        print_tenfa(&tenfa);
    }

    #[test]
    fn wikipedia() {
        let tenfa = regex::wikipedia().into();
        print_tenfa(&tenfa);
    }

    pub(crate) fn print_tenfa<A: Hash + Eq + Clone + Display>(enfa: &Tenfa<A>) {
        use super::State;
        let mut todo = Vec::from([&enfa.start]);
        let mut visited: Vec<&State> = Vec::new();

        print!(
            r#"
              digraph G {{
                  rankdir = TB;
                  node [ shape = circle ];
                  edge [ weight = 2 ];
                  node [ width = 0.3 ];
                  edge [ weight = 2 ];
                  root = start;
                  start [ shape = none, label = "" ];
                  start -> {:?}
                  {} [ shape = doublecircle ]
            "#,
            enfa.start, enfa.accept
        );

        use super::Edge;
        fn format_transition<A: Hash + Eq + Clone + Display>(
            src: State,
            edge: Edge<A>,
            dst: State,
        ) {
            match edge {
                Edge::Step(sym) => {
                    println!(r#"    {src} -> {dst} [label = "{sym}" color = "blue4"];"#);
                },
                Edge::Epsilon(Some((sign, tag))) => {
                    let sign = if sign { "+" } else { "-" };
                    println!(r#"    {src} -> {dst} [label = "{sign}{tag}" color = "green"];"#);
                },
                Edge::Epsilon(None) => {
                    println!(r#"    {src} -> {dst} [color = "cyan3"];"#);
                },
            }
        }

        while let Some(src) = todo.pop() {
            if visited.contains(&src) {
                continue;
            } else {
                visited.push(src);
            }

            let transitions = enfa
                .transitions
                .get(src)
                .into_iter()
                .flatten()
                .flat_map(|(edge, dsts)| dsts.into_iter().map(move |dst| (edge, dst)));

            for (edge, dst) in transitions {
                format_transition(*src, edge.clone(), *dst);
                todo.push(dst);
            }
        }

        let transitions = enfa
            .transitions
            .clone()
            .into_iter()
            .flat_map(|(src, steps)| steps.into_iter().map(move |(edge, dsts)| (src, edge, dsts)))
            .flat_map(|(src, edge, dsts)| {
                dsts.into_iter().map(move |dst| (src, edge.clone(), dst))
            });

        let unvisited =
            transitions.filter(|(src, _, dst)| !visited.contains(&src) || !visited.contains(&dst));
        let mut unvisited = unvisited.peekable();
        if let Some(_) = unvisited.peek() {
            println!("// UNVISITED");
            while let Some((src, edge, dst)) = unvisited.next() {
                format_transition(src, edge, dst);
            }
        }

        println!(r#"}}"#);
    }
}
