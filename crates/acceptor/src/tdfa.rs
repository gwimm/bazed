use std::{
    collections::{HashMap, HashSet},
    hash::{Hash, Hasher}, fmt::Display,
};

use itertools::Itertools;

use crate::{
    common::{IterExt, HashMapExt, Id},
    tenfa::{self, Tenfa},
};

enum Oper {
    // p
    Load,
    Copy(usize),
}

type Config = HashMap<Id, Option<Oper>>;
// struct Closure<A>(A, Config);

// impl<A: Hash> Hash for Closure<A> {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         self.0.hash(state);
//     }
// }
// 
// type State = Closure<Id>;
// type Delta<A> = (State, Closure<A>, State);

// struct Deltas<A>(HashMap<State, HashMap<Closure<A>, State>>);

struct Tdfa<A> {
    start: tenfa::State,
    goals: HashSet<tenfa::State>,
    edges: tenfa::Deltas<A>,
    reg_count: usize,
}


fn format_table<T: Display>(
    title: T,
    state: &HashMap<tenfa::State, HashSet<(bool, usize)>>
) -> String {
    let table = state.into_iter()
        .sorted_unstable_by(|(l, ..), (r, ..)| r.0.cmp(&l.0))
        .map(|(id, tags)| {
            let tags = tags.into_iter()
                .sorted_unstable_by(|(_, ref l), (_, r)| r.cmp(l))
                .map(|(sign, tag)| {
                    let sign = if *sign { "&nbsp;" } else { "−" };
                    format!("<i>{sign}t</i><sub>{tag}</sub> ")
                })
                .collect::<String>();

            let lad = format!(r#"<td port="lookahead{id}" align="left">{tags}</td>"#);
            format!(
                r#"<tr><td port="state{id}">{id}</td>{lad}</tr>"#,
            )
        })
        .collect::<String>();

    let header = "<tr><td><i>state</i></td><td><i>la</i></td></tr>";
    let title = format!(r#"<tr><td colspan="2">TDFA {title}</td></tr>"#);
    let attrs = r#"border="0" cellborder="1" cellspacing="0""#;
    format!("<table {attrs}>{title}{header}{table}</table>")
}

type Closure = HashMap<tenfa::State, HashSet<(bool, usize)>>;

fn enclose<A: Eq + Hash>( // FIXME: A isn't required, nor is Eq + Hash
    mut edges: tenfa::Deltas<&A>,
    start: tenfa::State,
) -> Closure {
    let eps = edges.drain_epsilon_closure(&start);
    let (mut closure, goals) = eps
        .fold(
            (
                HashMap::from([(start, HashSet::new())]),
                HashSet::<tenfa::State>::new(),
            ),
            |(mut closure, mut goals), (src, epsilon, dst)| {
                goals.insert(dst);
                goals.remove(&src);
                let mut config = closure[&src].clone();
                if let Some(tag) = epsilon.tagged() {
                    config.insert(tag);
                }
                closure.insert(dst, config);
                (closure, goals)
            }
        );   

    closure.retain(|state, _| goals.contains(state));
    closure
}

fn get_step<'a, A: Eq + Hash>(
    edges: tenfa::Deltas<&'a A>,
    src: &tenfa::State,
) -> Option<(&'a A, tenfa::State)> {
    edges.0
        .get(&src)
        .into_iter()
        .flatten()
        .map(|(edge, dst)| (edge.as_ref(), *dst))
        .find_map(|(edge, dst)| edge.deter().map(|sym| (*sym, dst)))
}

impl<A: Eq + Hash + Clone + std::fmt::Debug> Tdfa<A> {

    // determinization(Σ, T, Q, q0, qf, Δ)
    // 01  S, Sf : empty sets of states
    // 02  δ : undefined transition function
    // 03  φ : undefined final function
    // 04  r0 = {1, ... , |T|}, Rf = {|T|+1, ... , 2|T|}, R = {r0} ∪ Rf
    // 05  C = epsilon closure({(q0, r0, ε, ε)})
    // 06  P = precedence(C)
    // 07  s0 = add state(S, Sf, Rf, φ, C, P, ε)
    // 08  for each state s ∈ S do
    // 09      V : map from tag and operation RHS to register
    // 10      for each symbol a ∈ Σ do
    // 11          B = step on symbol(s, a)
    // 12          C = epsilon closure(B)
    // 13          O = transition regops(C, R, V )
    // 14          P = precedence(C)
    // 15          s' = add state(S, Sf, Rf, φ, C, P, O)
    // 16          δ(s, a) = (s', O)
    // 17  return TDFA (Σ, T, S, Sf, s0, R, Rf, δ, φ)

    fn determinize(tenfa: Tenfa<A>) -> Self {
        let edges = tenfa.edges;

        lrt state0 = enclose(edges.as_ref(), tenfa.start);
        println!("    state0 [label = <{}>];", format_table("state 0", &state0));

        let x = state0
            .clone()
            .into_iter()
            .filter_map(|(src, la)| {
                get_step(edges.as_ref(), &src)
                    .map(|(sym, dst)| (sym, (src, la, dst)))
            })
            .into_grouping_map()
            .fold(
                HashMap::<tenfa::State, (tenfa::State, HashSet<(bool, usize)>)>::new(),
                |mut acc, _sym, (src, _la, dst)| {
                    let x = enclose(edges.as_ref(), dst)
                        .into_iter()
                        .map(|(dst, la)| (dst, (src, la)));
                    acc.extend(x);
                    acc
                },
            );

        x.iter().enumerate().for_each(|(i, (_sym, clos))| {
            let i = i + 1;

            clos.into_iter()
                .for_each(|(dst, (src, _))| {
                    println!("    state0:lookahead{src} -> state{i}:state{dst}");
                });

            let table: HashMap<Id, HashSet<(bool, usize)>> = clos
                .into_iter()
                .map(|(dst, (_src, la))| (*dst, la.clone()))
                .collect();

            println!(
                "    state{i} [label = <{}>];",
                format_table(format!("state {i}"), &table),
            );
        });

        todo!();
    }

    // add_state(S, Sf, Rf, φ, C, P, O)
    // 18  X = {(q, r, l) | (q, r, _, l) ∈ C}
    // 19  s = (X, P)
    // 20  if s ∈ S then
    // 21      return s
    // 22  else if ∃s' ∈ S such that map(s, s', O) then
    // 23      return s'
    // 24  else
    // 25      add s to S
    // 26      if ∃(q, r, l) ∈ X such that q = qf then
    // 27          add s to Sf
    // 28          φ(s) = final regops(Rf, r, l)
    // 29      return s 

    // map((X, P), (X', P '), O)
    // 30  if X and X' have different subsets of TNFA states
    // 31      or different lookahead tags for some TNFA state
    // 32      or precedence is different: P ≠ P ' then
    // 33      return false
    // 34  M, M' : empty maps from register to register
    // 35  for each pair (q, r, l) ∈ X and (q, r', l) ∈ X' do
    // 36      for each t ∈ T do
    // 37          if history(l, t) = ϵ or t is a multi-tag then
    // 38              i = r[t], j = r'[t]
    // 39              if both M[i], M '[j] are undefined then
    // 40                  M[i] = j, M '[j] = i
    // 41              else if M[i] ̸= j or M '[j] ̸= i then
    // 42                  return false
    // 43  for each operation i ← in O do
    // 44      replace register i with M[i]
    // 45      remove pair (i, M[i]) from M
    // 46  for each pair (j, i) ∈ M where j ̸= i do
    // 47      prepend copy operation i ← j to O
    // 48  return topological sort(O)

    // transition_regops(C, R, V)
    // 66  O : empty list of operations
    // 67  for each (q, r, h, l) ∈ C do
    // 68      for each tag t ∈ T do
    // 69          if ht = history(h, t) ̸= ϵ then
    // 70              v = regop rhs(r, ht, t)
    // 71              if V [t][v] is undefined then
    // 72                  i = max{R} + 1
    // 73                  R = R ∪ {i}
    // 74                  V [t][v] = i
    // 75                  append operation i ← v to O
    // 76              r[t] = V [t][v]
    // 77  return O 
}

#[cfg(test)]
mod test {
    use super::{ tenfa, Tdfa };

    #[test]
    fn determinize() {
        let tenfa = tenfa::test::re2c_paper();
        tenfa::test::print(&tenfa);
        Tdfa::determinize(tenfa);
    }
}
