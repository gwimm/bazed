use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet, VecDeque},
    hash::Hash,
    ops::Range,
};

use itertools::Itertools;

use crate::common::{IterExt, Id};

pub(crate) type State = Id;

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

pub fn sequence<A, I: IntoIterator<Item = Regex<A>>>(iter: I) -> Option<Regex<A>> {
    iter.into_iter()
        .reduce(|acc, rx| Regex::Alternative(Box::new(acc), Box::new(rx)))
}

pub fn seq<A>(rx1: Regex<A>, rx2: Regex<A>) -> Regex<A> {
    Regex::Sequence(Box::new(rx1), Box::new(rx2))
}

#[cfg(test)]
mod regex_test {
    use super::{alt, many, seq, sequence, Regex};

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
        seq(digit1(), many(digit()))
    }

    pub(crate) fn re2c_paper() -> Regex<char> {
        let a = Regex::Symbol('a');
        let b = Regex::Symbol('b');
        // let an = many(sequence([Regex::Tag, a.clone(), Regex::Tag]).unwrap());
        // let ab = alt(a, seq(b.clone(), Regex::Tag));
        // sequence([an, Regex::Tag, ab, Regex::Tag, many(b)]).unwrap()
        let an = many(seq(Regex::Tag, seq(a.clone(), Regex::Tag)));
        let ab = alt(a, seq(Regex::Tag, b.clone()));
        seq(an, seq(Regex::Tag, seq(ab, seq(Regex::Tag, many(b)))))
    }

    pub(crate) fn wikipedia() -> Regex<char> {
        let t = Regex::Tag;
        let a = Regex::Symbol('a');
        let b = Regex::Symbol('b');
        alt(sequence([a.clone(), t, many(b.clone())]).unwrap(), seq(a, b))
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Epsilon {
    Tagged(bool, usize),
    Epsilon(usize),
}

impl Epsilon {
    pub(crate) fn tagged(self) -> Option<(bool, usize)> {
        if let Self::Tagged(sign, tag) = self {
            Some((sign, tag))
        } else {
            None
        }
    }
}

#[derive(Hash, Clone, PartialEq, Eq)]
pub(crate) enum Edge<A> {
    Deter(A),
    Epsilon(Epsilon),
}

impl<A> Edge<A> {
    fn new_epsilon(priority: usize) -> Edge<A> {
        Edge::Epsilon(Epsilon::Epsilon(priority))
    }

    fn new_tag(sign: bool, tag: usize) -> Edge<A> {
        Edge::Epsilon(Epsilon::Tagged(sign, tag))
    }

    pub(crate) fn as_ref(&self) -> Edge<&A> {
        match self {
            Edge::Deter(a) => Edge::Deter(a),
            Edge::Epsilon(e) => Edge::Epsilon(*e),
        }
    }

    pub(crate) fn tagged(self) -> Option<(bool, usize)> {
        self.epsilon().and_then(|e| e.tagged())
    }

    pub(crate) fn epsilon(self) -> Option<Epsilon> {
        if let Self::Epsilon(edge) = self {
            Some(edge)
        } else {
            None
        }
    }

    pub(crate) fn deter(self) -> Option<A> {
        if let Self::Deter(a) = self {
            Some(a)
        } else {
            None
        }
    }

    pub(crate) fn is_deter(&self) -> bool {
        self.as_ref().deter().is_some()
    }
}

type Delta<A> = (State, Edge<A>, State);

#[derive(Clone)]
pub(crate) struct Deltas<A>(pub(crate) HashMap<State, HashMap<Edge<A>, State>>);

impl<A: Eq + Hash> Extend<Delta<A>> for Deltas<A> {
    fn extend<T: IntoIterator<Item = Delta<A>>>(&mut self, iter: T) {
        for edge in iter {
            self.extend_one(edge);
        }
    }

    fn extend_one(&mut self, (src, edge, dst): Delta<A>) {
        self.0.entry(src).or_default().insert(edge, dst);
    }
}

impl<A: Eq + Hash> Extend<(State, HashMap<Edge<A>, State>)> for Deltas<A> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (State, HashMap<Edge<A>, State>)>,
    {
        for (src, steps) in iter {
            let transitions = self.0.entry(src).or_default();
            transitions.extend(steps);
        }
    }
}

struct EdgesDrain<'a, A> {
    togo: VecDeque<(State, Edge<A>, State)>,
    edges: &'a mut Deltas<A>,
}

impl<'a, A> Iterator for EdgesDrain<'a, A> {
    type Item = Delta<A>;

    fn next(&mut self) -> Option<Self::Item> {
        self.togo
            .pop_front()
            .map(|(src, src_mid, mid)| {
                self.edges.drain(&mid)
                    .reversed()
                    .map(|(mid_dst, dst)| (mid, mid_dst, dst))
                    .for_each(|x| self.togo.push_back(x));

                (src, src_mid, mid)
            })
    }
}

struct EpsilonClosure<'a, A> {
    togo: VecDeque<(State, Epsilon, State)>,
    edges: &'a mut Deltas<A>,
}

impl<'a, A> Iterator for EpsilonClosure<'a, A> {
    type Item = (State, Epsilon, State);

    fn next(&mut self) -> Option<Self::Item> {
        self.togo
            .pop_front()
            .map(|(src, src_mid, mid)| {
                self.edges
                    .drain_epsilons(&mid)
                    .reversed()
                    .for_each(|(mid_dst, dst)| self.togo.push_back((mid, mid_dst, dst)));

                (src, src_mid, mid)
            })
    }
}

impl<A> Deltas<A> {
    fn new() -> Self {
        Self(HashMap::new())
    }

    pub(crate) fn drain_traverse<'a>(&'a mut self, src: &State)
        -> impl 'a + Iterator<Item = Delta<A>> {
        EdgesDrain {
            togo: self.drain(src).map(|(edge, dst)| (*src, edge, dst)).collect(),
            edges: self,
        }
    }

    pub(crate) fn drain_epsilon_closure<'a>(&'a mut self, src: &State)
        -> impl 'a + Iterator<Item = (State, Epsilon, State)> {
        EpsilonClosure {
            togo: self.drain_epsilons(src).map(|(edge, dst)| (*src, edge, dst)).collect(),
            edges: self,
        }
    }

    pub(crate) fn drain(&mut self, src: &State) -> impl Iterator<Item = (Edge<A>, State)> {
        self.0
            .remove(src)
            .into_iter()
            .flatten()
            .sorted_unstable_by(|(lhs, _), (rhs, _)| match (lhs, rhs) {
                (Edge::Epsilon(Epsilon::Epsilon(lhs)), Edge::Epsilon(Epsilon::Epsilon(rhs))) => {
                    lhs.cmp(rhs)
                },
                _ => Ordering::Equal,
            })
    }

    pub(crate) fn drain_epsilons(&mut self, src: &State) -> impl Iterator<Item = (Epsilon, State)> {
        self.drain(src)
            .filter_map(|(mid_dst, dst)| mid_dst.epsilon().map(|mid_dst| (mid_dst, dst)))
    }
}

impl<A: Eq + Hash> Deltas<A> {
    pub(crate) fn into_set(self) -> HashSet<(State, Edge<A>, State)> {
        self.0
            .into_iter()
            .flat_map(|(src, step)| step.into_iter().map(move |(edge, dst)| (src, edge, dst)))
            .collect()
    }

    pub(crate) fn iter_from(&self, src: &State) -> impl Iterator<Item = (Edge<&A>, State)> {
        self.as_ref().drain(src)
    }

    pub(crate) fn as_ref(&self) -> Deltas<&A> {
        let delta = self
            .0
            .iter()
            .map(|(id, steps)| {
                (
                    *id,
                    steps
                        .into_iter()
                        .map(|(edge, dst)| (edge.as_ref(), *dst))
                        .collect(),
                )
            })
            .collect();

        Deltas(delta)
    }

    fn step_from(&self, src: &State, sym: &A) -> Option<State> {
        self.steps_from(src).get(sym).copied()
    }

    fn steps_from(&self, src: &State) -> HashMap<&A, State> {
        self.iter_from(src)
            .filter_map(|(edge, dst)| edge.deter().map(|step| (step, dst)))
            .collect()
    }

    fn epsilons_from(&self, src: &State) -> HashMap<Epsilon, State> {
        self.iter_from(src)
            .filter_map(|(edge, dst)| edge.epsilon().map(|e| (e, dst)))
            .collect()
    }

    pub(crate) fn step_simulation(&self, sim: Simulation, sym: &A) -> Simulation {
        Simulation {
            offset: sim.offset + 1,
            configs: sim
                .configs
                .into_iter()
                .filter_map(|(src, rs)| self.step_from(&src, sym).map(move |dst| (dst, rs.clone())))
                .map(move |(state, rs)| (state.clone(), rs))
                .collect(),
        }
    }

    pub(crate) fn epsilon_closure(&self, accept: &State, sim: Simulation) -> Simulation {
        let mut stack = sim.configs;
        stack.reverse();

        let mut cfgs = Vec::new();
        while let Some((src, src_regs)) = stack.pop() {
            cfgs.push((src, src_regs.clone()));

            let dst_cfgs = self
                .epsilons_from(&src)
                .into_iter()
                .filter(|(_, dst)| cfgs.iter().any(|(state, _)| state == dst))
                .map(|(ep, dst)| {
                    let mut regs = src_regs.clone();
                    if let Some((sign, tag)) = ep.tagged() {
                        regs[tag as usize] = sign.then_some(sim.offset);
                    }

                    (dst, regs)
                });

            stack.extend(dst_cfgs);
        }

        // only retain determined steps and final states
        cfgs.retain(|(state, _)| !self.steps_from(state).is_empty() || state == accept);

        Simulation {
            offset: sim.offset,
            configs: cfgs,
        }
    }
}

#[derive(Clone)]
pub struct Tenfa<A> {
    pub(crate) start: State,
    pub(crate) accept: State,
    pub(crate) tag_count: usize,
    pub(crate) edges: Deltas<A>,
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

impl<A: Hash + Eq + Clone> From<Regex<A>> for Tenfa<A> {
    fn from(regex: Regex<A>) -> Self {
        let mut tenfa = Self::epsilon();
        tenfa.regex_extend(regex);
        tenfa
    }
}

impl<A> Tenfa<A> {
    fn epsilon() -> Self {
        let accept = State::gen();
        Self {
            start: accept,
            accept,
            tag_count: 0,
            edges: Deltas::new(),
        }
    }
}

impl<A: Hash + Eq> Tenfa<A> {
    pub(crate) fn as_ref(&self) -> Tenfa<&A> {
        let Self { start, accept, tag_count, edges } = self;
        Tenfa {
            start: *start,
            accept: *accept,
            tag_count: *tag_count,
            edges: edges.as_ref(),
        }
    }
}

impl<A: Hash + Eq + Clone> Tenfa<A> {
    fn regex_extend(&mut self, rx: Regex<A>) {
        match rx {
            Regex::Tag => self.extend_tag(),
            Regex::Symbol(sym) => self.extend_deter(sym),
            Regex::Sequence(lhs, rhs) => self.regex_extend_seq(*lhs, *rhs),
            Regex::Alternative(lhs, rhs) => self.regex_extend_alt(*lhs, *rhs),
            Regex::Repetition(rx, low, count) => self.regex_extend_rep(*rx, low, count),
        }
    }

    fn regex_extend_rep(&mut self, rx: Regex<A>, low: usize, count: Option<usize>) {
        match (low, count) {
            (0, Some(0)) => panic!("optional never"),
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
            (1, Some(0)) => self.regex_extend(rx),
            (1, Some(count @ 1..)) => {
                // if m == 1 then ?
                let accept = self.start;
                self.regex_extend_rep(rx.clone(), 1, Some(count - 1));
                self.binary_epsilon_branch(accept, self.start);
                self.regex_extend(rx);
            },
            (1, None) => {
                // +
                self.extend_edge(Edge::new_epsilon(1));
                let accept = self.start;
                self.regex_extend(rx);
                self.edges.extend_one((accept, Edge::new_epsilon(0), self.start));
            },
            (low @ 2.., count) => {
                self.regex_extend_rep(rx.clone(), low - 1, count);
                self.regex_extend(rx);
            },
            _ => unreachable!(),
        }
    }

    fn regex_extend_seq(&mut self, lhs: Regex<A>, rhs: Regex<A>) {
        self.regex_extend(rhs);
        self.regex_extend(lhs);
    }

    fn regex_extend_alt(&mut self, right: Regex<A>, left: Regex<A>) {
        let accept = self.start;
        let accept_tag_count = self.tag_count;

        self.regex_extend(left);
        let left_start = self.start;
        let left_tag_count = self.tag_count;

        self.start = accept;
        self.negative_tags_extend(accept_tag_count..left_tag_count);
        self.regex_extend(right);
        let right_start = self.start;
        let right_tag_count = self.tag_count;

        self.start = left_start;
        self.negative_tags_extend(left_tag_count..right_tag_count);

        self.binary_epsilon_branch(right_start, self.start);
    }

    fn extend_deter(&mut self, sym: A) {
        self.extend_edge(Edge::Deter(sym));
    }

    fn extend_tag(&mut self) {
        self.extend_edge(Edge::new_tag(true, self.tag_count));
        self.tag_count += 1;
    }

    fn extend_edge(&mut self, edge: Edge<A>) {
        let start = State::gen();
        self.edges.extend_one((start, edge, self.start));
        self.start = start;
    }

    fn binary_epsilon_branch(&mut self, lhs: State, rhs: State) {
        self.start = State::gen();
        self.edges
            .extend_one((self.start, Edge::new_epsilon(0), rhs));
        self.edges
            .extend_one((self.start, Edge::new_epsilon(1), lhs));
    }

    fn negative_tags_extend(&mut self, tag_range: Range<usize>) {
        for tag in tag_range {
            self.extend_edge(Edge::new_tag(false, tag))
        }
    }
}

#[cfg(test)]
pub(crate) mod test {
 // use std::io::{Write, self};
    use std::{fmt::Display, hash::Hash};

    use super::{
        regex_test as regex,
        Tenfa, Deltas, State, Delta,
    };

    macro_rules! print_style {
        ($start:expr, $goal:expr) => {{
            println!(
                concat!(
                    r#"    start -> {:?}"#, "\n",
                    r#"    {} [ shape = doublecircle ]"#, "\n",
                ),
                $start,
                $goal,
            )
        }}
    }

    macro_rules! print_prelude {
        () => {{
            println!(
                concat!(
                    r#"digraph G {{"#, "\n",
                    r#"    rankdir = LR;"#, "\n",
                    r#"    node [ shape = circle ];"#, "\n",
                    r#"    edge [ weight = 2 ];"#, "\n",
                    r#"    node [ width = 0.3 ];"#, "\n",
                    r#"    edge [ weight = 2 ];"#, "\n",
                    r#"    root = start;"#, "\n",
                    r#"    start [ shape = none, label = "" ];"#, "\n",
                ),
            );
        }};
    }

    pub(crate) fn print_deltas<A: Hash + Eq + Clone + Display>(
        edges: &Deltas<A>,
        start: &State,
    ) {
        fn format_delta<A: Hash + Eq + Clone + Display>((src, edge, dst): Delta<A>) {
            use super::{Edge, Epsilon};
            let (label, color) = match edge {
                Edge::Deter(sym) => (format!(r#""{sym}""#), "blue4"),
                Edge::Epsilon(Epsilon::Epsilon(pre)) => (format!(r#""{pre}/ε""#), "cyan3"),
                Edge::Epsilon(Epsilon::Tagged(sign, tag)) => {
                    let sign = if sign { "+" } else { "-" };
                    (format!("<<i>{sign}t<sub>{tag}</sub></i>>"), "green")
                },
            };
            let style = format!(r#"label = {label}, color = "{color}""#);
            println!("    {src} -> {dst} [ {style} ];");
        }

        let mut graph = edges.as_ref();
        graph.drain_traverse(start).for_each(format_delta);

        let mut unvisited = graph
            .into_set()
            .into_iter()
            .peekable();

        if let Some(_) = unvisited.peek() {
            println!("    // UNVISITED");
            unvisited.for_each(format_delta)
        }
    }

    pub(crate) fn number() -> Tenfa<char> {
        regex::number().into()
    }

    pub(crate) fn re2c_paper() -> Tenfa<char> {
        regex::re2c_paper().into()
    }

    pub(crate) fn wikipedia() -> Tenfa<char> {
        regex::wikipedia().into()
    }

    #[test]
    fn print_re2c_paper() {
        let tenfa = Tenfa::from(re2c_paper());
        print(&tenfa);
    }

    pub(crate) fn print<A: Hash + Eq + Clone + Display>(tenfa: &Tenfa<A>) {
        print_prelude!();
        print_style!(tenfa.start, tenfa.accept);
        print_deltas(&tenfa.edges, &tenfa.start);
        println!(r#"}}"#);
    }
}
