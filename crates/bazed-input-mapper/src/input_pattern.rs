#![allow(unused)]
use std::{
    collections::HashMap,
    iter::{self, Peekable},
    ops::Range,
};

use dyn_clone::DynClone;
use itertools::Itertools;

use crate::{
    input_dfa::Nfa,
    input_event::{Key, KeyInput, Modifiers, RawKey},
};

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Combo {
    modifiers: Modifiers,
    key: String,
}
impl std::fmt::Debug for Combo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::fmt::Display for Combo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.modifiers.is_empty() {
            write!(f, "{}", self.key)
        } else {
            write!(f, "<{}-{}>", self.modifiers, self.key)
        }
    }
}

impl Combo {
    pub fn from_key(k: &str) -> Self {
        Self {
            modifiers: Modifiers::empty(),
            key: k.to_string(),
        }
    }
    pub fn matches(&self, input: &KeyInput) -> bool {
        input.modifiers == self.modifiers && input.key.0 == self.key
    }
}

#[derive(Debug, Clone)]
pub enum Repetition {
    Optional,
    ZeroOrMore,
    OneOrMore,
}

pub trait KeyPredicate: DynClone {
    fn check(&self, input: &KeyInput) -> bool;
}

dyn_clone::clone_trait_object!(KeyPredicate);

#[derive(Clone)]
pub enum InputPattern {
    Combo(Combo),
    Alternative(Vec<(String, InputPattern)>),
    OneOf(Vec<InputPattern>),
    Sequence(Vec<(String, InputPattern)>),
    Repeat(Repetition, Box<InputPattern>),
}

impl InputPattern {
    pub fn parse(
        &self,
        inputs: &mut Peekable<impl Iterator<Item = KeyInput>>,
    ) -> Option<InputMatch> {
        match self {
            InputPattern::Combo(c) => {
                if c.matches(inputs.peek()?) {
                    let k = inputs.next().unwrap();
                    Some(InputMatch::KeyInput(k))
                } else {
                    None
                }
            },
            InputPattern::Alternative(options) => options
                .iter()
                .find_map(|(name, pat)| Some((name, pat.parse(inputs)?)))
                .map(|(name, m)| InputMatch::Alternative(name.to_string(), Box::new(m))),
            InputPattern::OneOf(options) => options.iter().find_map(|pat| pat.parse(inputs)),
            InputPattern::Sequence(elems) => elems
                .iter()
                .map(|(name, pat)| Some((name.to_string(), pat.parse(inputs)?)))
                .collect::<Option<Vec<(String, InputMatch)>>>()
                .map(|entries| InputMatch::Sequence(entries.into_iter().collect())),
            InputPattern::Repeat(rep, pat) => match rep {
                Repetition::Optional => Some(InputMatch::List(
                    pat.parse(inputs).map(|x| vec![x]).unwrap_or_default(),
                )),
                Repetition::ZeroOrMore => {
                    let res = iter::from_fn(|| pat.parse(inputs)).collect();
                    Some(InputMatch::List(res))
                },
                Repetition::OneOrMore => {
                    let res: Vec<_> = iter::from_fn(|| pat.parse(inputs)).collect();
                    (res.len() > 0).then_some(InputMatch::List(res))
                },
            },
        }
    }
}

#[derive(Clone, Debug)]
pub enum InputMatch {
    KeyInput(KeyInput),
    Alternative(String, Box<InputMatch>),
    List(Vec<InputMatch>),
    Sequence(HashMap<String, InputMatch>),
}

impl InputMatch {
    fn unwrap_key_input(&self) -> &KeyInput {
        let Self::KeyInput(x) = self else { panic!("{self:?} was not a KeyInput") };
        x
    }
    fn unwrap_alt(&self) -> (&str, &InputMatch) {
        let Self::Alternative(x, x1) = self else { panic!("{self:?} was not an Alternative") };
        (x, x1)
    }
    fn unwrap_list(&self) -> &Vec<InputMatch> {
        let Self::List(x) = self else { panic!("{self:?} was not a List") };
        x
    }
    fn unwrap_seq(&self) -> &HashMap<String, InputMatch> {
        let Self::Sequence(x) = self else { panic!("{self:?} was not a Sequence") };
        x
    }
}

impl std::fmt::Debug for InputPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Combo(arg0) => f.debug_tuple("KeyInput").field(arg0).finish(),
            Self::Alternative(arg0) => f.debug_tuple("Alternative").field(arg0).finish(),
            Self::OneOf(arg0) => f.debug_tuple("OneOf").field(arg0).finish(),
            Self::Sequence(arg0) => f.debug_tuple("Sequence").field(arg0).finish(),
            Self::Repeat(arg0, arg1) => f.debug_tuple("Repeat").field(arg0).field(arg1).finish(),
        }
    }
}

pub fn key(k: &str) -> InputPattern {
    InputPattern::Combo(Combo::from_key(k))
}

macro_rules! alt {
    ($($name:literal => $pat:expr),*$(,)?) => {
        InputPattern::Alternative(vec![$(($name.to_string(), $pat)),*])
    }
}
macro_rules! seq {
    ($($name:literal => $pat:expr),*$(,)?) => {
        InputPattern::Sequence(vec![$(( $name.to_string(), $pat )),*])
    }
}
pub fn many1(x: InputPattern) -> InputPattern {
    InputPattern::Repeat(Repetition::OneOrMore, Box::new(x))
}
pub fn opt(x: InputPattern) -> InputPattern {
    InputPattern::Repeat(Repetition::Optional, Box::new(x))
}

fn digit() -> InputPattern {
    InputPattern::OneOf((0..10).map(|x| key(&x.to_string())).collect())
}

fn input() -> Vec<KeyInput> {
    vec![
        KeyInput {
            modifiers: Modifiers::empty(),
            key: Key("d".to_string()),
            code: RawKey("d".to_string()),
        },
        //KeyInput {
        //modifiers: Modifiers::empty(),
        //key: Key("2".to_string()),
        //code: RawKey("2".to_string()),
        //},
        KeyInput {
            modifiers: Modifiers::empty(),
            key: Key("2".to_string()),
            code: RawKey("2".to_string()),
        },
        KeyInput {
            modifiers: Modifiers::empty(),
            key: Key("w".to_string()),
            code: RawKey("w".to_string()),
        },
    ]
}

fn foo() -> InputPattern {
    let digit = InputPattern::OneOf((0..2).map(|x| key(&x.to_string())).collect());
    let number = many1(digit);
    let motion = alt!["next_word" => key("w"), "prev_word" => key("b")];
    let repeated_motion = seq!["count" => opt(number), "motion" => motion];
    let verb = alt!["delete" => key("d"), "change" => key("c")];
    let action = seq!["verb" => verb, "motion" => repeated_motion.clone()];
    let keymap = alt!["action" => action, "motion" => repeated_motion];
    keymap
}

#[test]
fn graphviz_lol() {
    let digit = InputPattern::OneOf((0..2).map(|x| key(&x.to_string())).collect());
    let number = many1(digit);
    let motion = alt!["next_word" => key("w"), "prev_word" => key("b")];
    let repeated_motion = seq!["count" => opt(number.clone()), "motion" => motion.clone()];
    let verb = alt!["delete" => key("d"), "change" => key("c")];
    let action = seq!["verb" => verb, "motion" => repeated_motion.clone()];
    let keymap = alt!["action" => action, "motion" => repeated_motion.clone()];

    let mut nfa = Nfa::from_input_pattern(keymap);
    nfa.minimize();

    println!("{}", nfa.to_graphviz());
}

#[test]
fn test_foo() {
    let pattern = foo();
    let input = input();
    let res = pattern.parse(&mut input.into_iter().peekable()).unwrap();

    #[derive(Debug)]
    enum Motion {
        NextWord,
        PrevWord,
    }
    #[derive(Debug)]
    enum Verb {
        Delete,
        Change,
    }

    fn interpret_number(m: &InputMatch) -> usize {
        m.unwrap_list()
            .into_iter()
            .flat_map(|x| x.unwrap_list().into_iter())
            .map(|x| x.unwrap_key_input().key.as_str())
            .join("")
            .parse::<usize>()
            .unwrap()
    }

    fn interpret_repeated_motion(m: &InputMatch) -> (usize, Motion) {
        let m = m.unwrap_seq();
        let count = interpret_number(&m["count"]);
        let motion = match m["motion"].unwrap_alt().0 {
            "next_word" => Motion::NextWord,
            "prev_word" => Motion::PrevWord,
            _ => unreachable!(),
        };
        (count, motion)
    }

    fn interpret_verb(m: &InputMatch) -> Verb {
        match m.unwrap_alt().0 {
            "delete" => Verb::Delete,
            "change" => Verb::Change,
            _ => unreachable!(),
        }
    }

    let alternative = res.unwrap_alt();
    match alternative.0 {
        "action" => {
            let s = alternative.1.unwrap_seq();
            let verb = interpret_verb(&s["verb"]);
            let motion = interpret_repeated_motion(&s["motion"]);
            println!("Action: {verb:?} {motion:?}");
        },
        "motion" => {
            let motion = interpret_repeated_motion(alternative.1);
            println!("Move: {motion:?}");
        },
        _ => unreachable!(),
    }

    //println!("{:#?}", res);
    panic!();
}
