use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::{common::Id, enfa::Enfa, regex::Regex};

type State = Id;
type EdgeId = Id;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Nfa<T>
where
    T: Hash + Eq,
{
    start: State,
    states: HashSet<State>,
    edges: HashMap<State, (EdgeId, HashMap<T, HashSet<State>>)>,
    accepts: HashSet<State>,

    capture_starts: HashSet<EdgeId>,
    capture_ends: HashSet<EdgeId>,
}

impl<T> From<Regex<T>> for Nfa<T>
where
    T: Hash + Eq + Clone,
{
    fn from(regex: Regex<T>) -> Self {
        Enfa::from(regex).into()
    }
}

impl<T> From<Enfa<T>> for Nfa<T>
where
    T: Hash + Eq + Clone,
{
    /// This removes epsilons from the Enfa to transform the Fa into an Nfa
    fn from(enfa: Enfa<T>) -> Self {
        let mut nfa: Nfa<T> = Nfa::new(enfa.start);
        if enfa.accept == enfa.start {
            nfa.accepts.insert(nfa.start);
        }

        let mut visited_eps: HashSet<(State, State)> = HashSet::new();
        let todo_epsilon = enfa
            .epsilons_from(&enfa.start)
            .into_iter()
            .map(|x| (enfa.start, None, *x));

        let mut todo: Vec<_> = enfa
            .edges_from(&enfa.start)
            .into_iter()
            .map(|(_, x, dst)| (enfa.start, Some(x.clone()), *dst))
            .chain(todo_epsilon)
            .collect();

        // iterate over transitions, starting with ε-transitions
        while let Some((q1, via, q2)) = todo.pop() {
            if let Some(alpha) = via {
                nfa.insert_edge(q1, alpha.clone(), q2);
                if enfa.accept == q2 {
                    nfa.accepts.insert(q2);
                }

                for q3 in enfa.epsilons_from(&q2).into_iter() {
                    if !nfa.contains_edge(&q1, &alpha, q3) {
                        todo.push((q1, Some(alpha.clone()), *q3));
                    }
                }

                for (_, via2, q3) in enfa.edges_from(&q2).into_iter() {
                    if !nfa.contains_edge(&q2, via2, q3) {
                        todo.push((q2, Some(via2.clone()), *q3));
                    }
                }
            } else {
                // transition is an ε-transititon
                visited_eps.insert((q1, q2));
                if enfa.accept == q2 {
                    nfa.accepts.insert(q1);
                }

                for (_, via2, q3) in enfa.edges_from(&q2).into_iter() {
                    if !nfa.contains_edge(&q1, via2, q3) {
                        todo.push((q1, Some(via2.clone()), *q3));
                    }
                }

                for q3 in enfa.epsilons_from(&q2) {
                    if !visited_eps.contains(&(q1, *q3)) {
                        todo.push((q1, None, *q3));
                    }
                }
            }
        }

        nfa
    }
}

impl<T> Nfa<T>
where
    T: Hash + Eq,
{
    pub fn new(start: State) -> Self {
        Self {
            start,
            accepts: HashSet::new(),
            states: HashSet::from([start]),
            edges: HashMap::new(),
            capture_starts: HashSet::new(),
            capture_ends: HashSet::new(),
        }
    }

    #[allow(dead_code)]
    fn from_transition(start: State, symbol: T, accept: State) -> Self {
        Self {
            start,
            accepts: HashSet::from([accept]),
            states: HashSet::from([start, accept]),
            edges: HashMap::from([(
                start,
                (
                    EdgeId::gen(),
                    HashMap::from([(symbol, HashSet::from([accept]))]),
                ),
            )]),
            capture_starts: HashSet::new(),
            capture_ends: HashSet::new(),
        }
    }

    pub fn next_states(&self, current: &State, input: &T) -> HashSet<State> {
        self.edges
            .get(current)
            .and_then(|(_, arrivals)| arrivals.get(&input).cloned())
            .unwrap_or_else(HashSet::new)
    }

    fn insert_edge(&mut self, src: State, edge: T, dst: State) {
        self.edges
            .entry(src)
            .or_insert_with(|| (EdgeId::gen(), HashMap::new()))
            .1
            .entry(edge)
            .or_default()
            .insert(dst);
    }

    #[allow(dead_code)]
    fn edges_from(
        &self,
        state: &State,
    ) -> impl IntoIterator<Item = (&EdgeId, &T, &HashSet<State>)> {
        self.edges
            .get(state)
            .into_iter()
            .flat_map(|(id, arrivals)| arrivals.into_iter().map(move |(sym, dst)| (id, sym, dst)))
    }

    fn contains_edge(&self, src: &State, edge: &T, dst: &State) -> bool {
        self.edges
            .get(src)
            .and_then(|arrivals| arrivals.1.get(edge))
            .map_or(false, |dsts| dsts.contains(dst))
    }
}

#[cfg(test)]
mod test {
    use super::Nfa;
    use crate::regex;

    #[test]
    fn match_single() {
        let regex = regex::sym('a');
        let nfa = Nfa::from(regex);
        let end = nfa
            .next_states(&nfa.start, &'a')
            .iter()
            .any(|state| nfa.accepts.contains(&state));

        assert!(end);
    }

    #[allow(dead_code)]
    fn trace_enfa<T: std::hash::Hash + Eq + Clone + std::fmt::Debug>(nfa: Nfa<T>) -> Nfa<T> {
        use super::State;
        let mut todo = Vec::from([&nfa.start]);
        let mut visited: Vec<&State> = Vec::new();
        // println!("====\nENFA\n  START: {}\n  ACCEPT: {}\n====", enfa.start, enfa.accept);
        print!(
            r#"digraph G {{
          rankdir = TB;
          node [ shape = circle ];
          edge [ weight = 2 ];
          node [ label = "", width = 0.3 ];
          edge [ weight = 2 ];
          root = start;
          start [ shape = none, label = "" ];
        "#
        );

        println!("          start -> {:?}", nfa.start);
        for accept in nfa.accepts.clone() {
            println!("          {accept} [ shape = doublecircle ];");
        }

        while let Some(src) = todo.pop() {
            if visited.contains(&src) {
                continue;
            } else {
                visited.push(src);
            }

            for (sym, dst) in nfa
                .edges_from(src)
                .into_iter()
                .flat_map(|(_, sym, dsts)| dsts.into_iter().map(move |dst| (sym, dst)))
            {
                println!(r#"  {src} -> {dst} [label = "{sym:?}"];"#);
                todo.push(dst);
            }
        }

        let transitions = nfa
            .edges
            .clone()
            .into_iter()
            .flat_map(|(src, (_, choices))| {
                choices.into_iter().map(move |(sym, dsts)| (src, sym, dsts))
            })
            .flat_map(|(src, sym, dsts)| dsts.into_iter().map(move |dst| (src, sym.clone(), dst)));

        let unvisited =
            transitions.filter(|(src, _, dst)| !visited.contains(&src) || !visited.contains(&dst));
        let mut unvisited = unvisited.peekable();
        if let Some(_) = unvisited.peek() {
            while let Some((src, sym, dst)) = unvisited.next() {
                println!(r#"  {src} -> {dst} [label = "{sym:?}"];"#);
            }
        }

        println!(r#"}}"#);

        nfa
    }

    #[test]
    fn match_number() {
        let nfa = trace_enfa(Nfa::from(regex::number()));

        let haystack = "1234567890".to_string();
        let mut states = Vec::from([nfa.start]);

        for digit in haystack.chars() {
            print!("before: {:?}, input: {:?}", states.len(), digit);
            states = states
                .iter()
                .map(|state| nfa.next_states(state, &digit))
                .flatten()
                .collect();
            println!("after: {:?}", states.len());
        }

        let is_accepting = states.iter().any(|state| nfa.accepts.contains(&state));
        println!("{:?}", states);
        assert!(is_accepting);
    }
}
