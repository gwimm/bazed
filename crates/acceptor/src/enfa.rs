//! Nondeterministic finite acceptor with epsilon moves (NFA-ε)

use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    iter::Extend,
};

use crate::{common::Id, regex::Regex};

type State = Id;
type EdgeId = Id;

#[derive(Clone)]
pub(crate) struct Enfa<T>
where
    T: Hash + Eq,
{
    pub(crate) start: State,
    pub(crate) accept: State,
    pub(crate) edges: HashMap<State, (EdgeId, HashMap<T, HashSet<State>>)>,
    pub(crate) epsilons: HashMap<State, HashSet<State>>,

    pub(crate) capture_starts: HashSet<EdgeId>,
    pub(crate) capture_ends: HashSet<EdgeId>,
}

impl<T> Extend<Enfa<T>> for Enfa<T>
where
    T: Hash + Eq,
{
    fn extend<I: IntoIterator<Item = Enfa<T>>>(&mut self, iter: I) {
        for enfa in iter.into_iter() {
            self.extend_one(enfa)
        }
    }

    /// Extend this NFA by another NFA, adding its states, edges and epsilons.
    /// start and accepting states
    fn extend_one(&mut self, mut other: Enfa<T>) {
        if let Some(other_from_start) = other.edges.remove(&other.start) {
            other.edges.insert(self.accept, other_from_start);
        }

        if let Some(other_epsilons_from_start) = other.epsilons.remove(&other.start) {
            other
                .epsilons
                .insert(self.accept, other_epsilons_from_start);
        }

        self.accept = other.accept;

        self.edges.extend(other.edges);
        self.epsilons.extend(other.epsilons);
        self.capture_starts.extend(other.capture_starts);
        self.capture_ends.extend(other.capture_ends);
    }
}

impl<T> From<Regex<T>> for Enfa<T>
where
    T: Hash + Eq,
{
    /// Generate an ε nondeterministic finite acceptor from a [Regex]
    fn from(pattern: Regex<T>) -> Enfa<T> {
        use crate::regex::Repeat;
        match pattern {
            Regex::Symbol(symbol) => Self::from_transition(State::gen(), symbol, State::gen()),
            Regex::Capture(name, box pat) => {
                let mut enfa = Enfa::from(pat);
                enfa.capture_as(name);
                enfa
            },
            Regex::Alternative(mut alts) => {
                let mut iter = alts.drain(..).map(Enfa::from);
                let mut enfa = Enfa::from(iter.next().unwrap());
                enfa.or(iter);
                enfa
            },
            Regex::Sequence(mut seq) => {
                let mut iter = seq.drain(..).map(Enfa::from);
                let mut enfa = Enfa::from(iter.next().unwrap());
                enfa.extend(iter);
                enfa
            },
            Regex::Repeat(rep, pat) => match rep {
                Repeat::Optional => {
                    let mut enfa = Enfa::from(*pat);
                    enfa.optional();
                    enfa
                },
                Repeat::NoneOrMore => {
                    let mut enfa = Enfa::from(*pat);
                    enfa.optional();
                    enfa.repeat();
                    enfa
                },
                Repeat::OneOrMore => {
                    let mut enfa = Enfa::from(*pat);
                    enfa.repeat();
                    enfa
                },
            },
        }
    }
}

impl<T> Enfa<T>
where
    T: Hash + Eq,
{
    #[allow(dead_code)]
    fn from_epsilon(start: State, accept: State) -> Self {
        Self {
            start,
            accept,
            edges: HashMap::new(),
            epsilons: HashMap::from([(start, HashSet::from([accept]))]),
            capture_starts: HashSet::new(),
            capture_ends: HashSet::new(),
        }
    }

    fn from_transition(start: State, symbol: T, accept: State) -> Self {
        Self {
            start,
            accept,
            edges: HashMap::from([(
                start,
                (
                    EdgeId::gen(),
                    HashMap::from([(symbol, HashSet::from([accept]))]),
                ),
            )]),
            epsilons: HashMap::new(),
            capture_starts: HashSet::new(),
            capture_ends: HashSet::new(),
        }
    }

    fn optional(&mut self) {
        self.insert_epsilon(self.start, self.accept);
    }

    fn repeat(&mut self) {
        let ((_, start), (accept, _)) = self.epsilon_wrap();
        self.insert_epsilon(accept, start);
    }

    fn epsilon_wrap(&mut self) -> ((State, State), (State, State)) {
        let start = self.epsilon_start();
        let accept = self.epsilon_accept();
        (start, accept)
    }

    // returns the ε-transition (new_start, old_start)
    fn epsilon_start(&mut self) -> (State, State) {
        let old_start = self.start;
        self.start = State::gen();
        self.insert_epsilon(self.start, old_start);
        (self.start, old_start)
    }

    // returns the ε-transition (old_accept, new_accept)
    fn epsilon_accept(&mut self) -> (State, State) {
        let old_accept = self.accept;
        self.accept = State::gen();
        self.insert_epsilon(old_accept, self.accept);
        (old_accept, self.accept)
    }

    // do not call function without adding a transition to `other.start`
    fn naive_extend_one(&mut self, other: Enfa<T>) {
        self.edges.extend(other.edges);
        for (src, dsts) in other.epsilons {
            self.epsilons.entry(src).or_default().extend(dsts);
        }
        self.capture_starts.extend(other.capture_starts);
        self.capture_ends.extend(other.capture_ends);
    }

    fn naive_extend<I: IntoIterator<Item = Enfa<T>>>(&mut self, iter: I) {
        for other in iter {
            self.naive_extend_one(other);
        }
    }

    fn or<I: IntoIterator<Item = Enfa<T>>>(&mut self, alts: I) {
        let (start, _) = self.epsilon_start();
        let (_, accept) = self.epsilon_accept();
        self.naive_extend(alts.into_iter().map(|mut alt| {
            alt.insert_epsilon(start, alt.start);
            alt.insert_epsilon(alt.accept, accept);
            alt
        }));
    }

    fn capture_as(&mut self, _name: String) {
        let from_start: HashSet<EdgeId> = self
            .edges_from(&self.start)
            .into_iter()
            .map(|(id, ..)| id)
            .cloned()
            .collect();

        let to_accept: HashSet<EdgeId> = self
            .edges_to(&self.accept)
            .into_iter()
            .map(|(id, ..)| id)
            .cloned()
            .collect();

        self.capture_starts.extend(from_start);
        self.capture_ends.extend(to_accept);
    }

    /// Insert epsilon transition into the [Enfa]
    fn insert_epsilon(&mut self, src: State, dst: State) {
        self.epsilons.entry(src).or_default().insert(dst);
    }

    /// Insert transition into the [Enfa]
    #[allow(dead_code)]
    fn insert_edge(&mut self, src: State, edge: T, dst: State) {
        self.edges
            .entry(src)
            .or_insert_with(|| (EdgeId::gen(), HashMap::new()))
            .1
            .entry(edge)
            .or_default()
            .insert(dst);
    }

    /// This is strange, edges do not have a designated order, though this return type encodes one
    /// also this name `iter_over_edges_from` is subject to change, specifically to
    /// `edges_iter_from`
    pub(crate) fn edges_from(&self, state: &State) -> HashSet<(&EdgeId, &T, &State)> {
        self.edges
            .get(state)
            .into_iter()
            .flat_map(|(id, inputs)| {
                inputs
                    .iter()
                    .map(move |(input, states)| (id, input, states))
            })
            .flat_map(|(id, input, states)| states.iter().map(move |state| (id, input, state)))
            .collect()
    }

    pub(crate) fn edges_to(&self, state: &State) -> HashSet<(&EdgeId, &T, &State)> {
        self.edges
            .iter()
            .flat_map(|(src, (id, arrivals))| {
                arrivals.iter().map(move |(via, dsts)| (id, src, via, dsts))
            })
            .flat_map(|(id, src, via, dsts)| dsts.iter().map(move |dst| (id, src, via, dst)))
            .filter_map(|(id, src, via, dst)| {
                if dst == state {
                    Some((id, via, src))
                } else {
                    None
                }
            })
            .collect()
    }

    #[allow(dead_code)]
    pub(crate) fn epsilons_from(&self, s: &State) -> HashSet<&State> {
        self.epsilons
            .get(s)
            .into_iter()
            .flat_map(|x| x.iter())
            .collect()
    }

    #[allow(dead_code)]
    pub(crate) fn epsilons_to(&self, dst: &State) -> HashSet<&State> {
        self.epsilons
            .iter()
            .flat_map(|(src, dsts)| dsts.iter().map(move |dst| (src, dst)))
            .filter_map(|(src, dst1)| if dst == dst1 { Some(src) } else { None })
            .collect()
    }
}

#[cfg(test)]
mod test {
    use super::{Enfa, State};
    use crate::regex;

    fn example_alt() -> Enfa<char> {
        let mut iter = "abc"
            .chars()
            .map(|c| Enfa::from_transition(State::gen(), c, State::gen()));
        let mut enfa = iter.next().unwrap();
        enfa.or(iter);
        enfa
    }

    fn example_alt_regex() -> Enfa<char> {
        Enfa::from(regex::alt("abc".chars().map(|c| regex::sym(c))))
    }

    fn example_seq() -> Enfa<char> {
        let mut iter = "abc"
            .chars()
            .map(|c| Enfa::from_transition(State::gen(), c, State::gen()));
        let mut enfa = iter.next().unwrap();
        enfa.extend(iter);
        enfa
    }

    fn example_seq_regex() -> Enfa<char> {
        Enfa::from(regex::seq("abc".chars().map(|c| regex::sym(c))))
    }

    fn example_opt() -> Enfa<char> {
        let mut enfa = Enfa::from_transition(State::gen(), 'a', State::gen());
        enfa.optional();
        enfa
    }

    fn example_opt_regex() -> Enfa<char> {
        Enfa::from(regex::opt(regex::sym('a')))
    }

    fn example_rep() -> Enfa<char> {
        let mut enfa = Enfa::from_transition(State::gen(), 'a', State::gen());
        enfa.repeat();
        enfa
    }

    fn example_rep_regex() -> Enfa<char> {
        Enfa::from(regex::many(regex::sym('a')))
    }

    fn is_thompson(enfa: &Enfa<char>) -> bool {
        let edges =
            enfa.edges_to(&enfa.start).is_empty() && enfa.edges_from(&enfa.accept).is_empty();
        let epsilons =
            enfa.epsilons_to(&enfa.start).is_empty() && enfa.epsilons_from(&enfa.accept).is_empty();
        edges && epsilons
    }

    #[test]
    fn alt() {
        assert!(is_thompson(&trace_enfa(example_alt())));
        assert!(is_thompson(&trace_enfa(example_alt_regex())));
    }

    #[test]
    fn seq() {
        assert!(is_thompson(&trace_enfa(example_seq())));
        assert!(is_thompson(&trace_enfa(example_seq_regex())));
    }

    #[test]
    fn opt() {
        assert!(is_thompson(&trace_enfa(example_opt())));
        assert!(is_thompson(&trace_enfa(example_opt_regex())));
    }

    #[test]
    fn rep() {
        assert!(is_thompson(&trace_enfa(example_rep())));
        assert!(is_thompson(&trace_enfa(example_rep_regex())));
    }

    #[test]
    fn number() {
        _ = trace_enfa(Enfa::from(regex::number()));
    }

    #[test]
    fn wikipedia() {
        let a = regex::sym('a');
        let b = regex::sym('b');
        let t = regex::sym('t');
        let alt1 = regex::seq([regex::many(a.clone()), t, regex::many(b.clone())]);
        let regex = regex::alt([alt1, regex::seq([a, b])]);
        _ = trace_enfa(Enfa::from(regex));
    }

    #[test]
    fn worst_case() {
        use regex::Regex;
        fn gen<const N: usize>() -> Regex<bool> {
            // /(a|b)*a{n}ab/
            let a = regex::sym(true);
            let b = regex::sym(false);
            let alt = regex::alt([a.clone(), b.clone()]);
            let mut seq = vec![regex::many(alt.clone()), a.clone()];
            seq.extend((0..N).into_iter().map(|_| alt.clone()));
            regex::seq(seq)
        }
        _ = trace_enfa(Enfa::from(gen::<9>()));
    }

    use std::{fmt::Display, hash::Hash};

    pub(crate) fn trace_enfa<T: Hash + Eq + Clone + Display>(enfa: Enfa<T>) -> Enfa<T> {
        let mut todo = Vec::from([&enfa.start]);
        let mut visited: Vec<&State> = Vec::new();
        // println!("====\nENFA\n  START: {}\n  ACCEPT: {}\n====", enfa.start, enfa.accept);
        print!(
            r#"digraph G {{
          rankdir = TB;
          node [ shape = circle ];
          edge [ weight = 2 ];
          node [ width = 0.3 ];
          edge [ weight = 2 ];
          root = start;
          start [ shape = none, label = "" ];
        "#
        );

        println!("          start -> {:?}", enfa.start);
        println!("          {} [ shape = doublecircle ];", enfa.accept);

        while let Some(src) = todo.pop() {
            if visited.contains(&src) {
                continue;
            } else {
                visited.push(src);
            }

            for (_, sym, dst) in enfa.edges_from(src) {
                println!(r#"          {src} -> {dst} [label = "{sym}" color = "blue"];"#);
                todo.push(dst);
            }

            for dst in enfa.epsilons_from(src) {
                println!(r#"          {src} -> {dst} [color = "green"];"#);
                todo.push(dst);
            }
        }

        println!(r#"}}"#);

        let epsilons = enfa
            .epsilons
            .clone()
            .into_iter()
            .flat_map(|(src, dsts)| dsts.into_iter().map(move |dst| (src, None, dst)));

        let transitions = enfa
            .edges
            .clone()
            .into_iter()
            .flat_map(|(src, (_, choices))| {
                choices.into_iter().map(move |(sym, dsts)| (src, sym, dsts))
            })
            .flat_map(|(src, sym, dsts)| {
                dsts.into_iter()
                    .map(move |dst| (src, Some(sym.clone()), dst))
            })
            .chain(epsilons);

        let unvisited =
            transitions.filter(|(src, _, dst)| !visited.contains(&src) || !visited.contains(&dst));
        let mut unvisited = unvisited.peekable();
        if let Some(_) = unvisited.peek() {
            println!("=== UNVISITED");
            while let Some((src, sym, dst)) = unvisited.next() {
                if let Some(sym) = sym {
                    println!("  {src} == {sym} => {dst}")
                } else {
                    println!("  {src} => {dst}")
                }
            }
        }
        enfa
    }
}
