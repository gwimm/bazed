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
        write!(f, "{self}")
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
    pub fn from_input(input: KeyInput) -> Self {
        Self {
            modifiers: input.modifiers,
            //TODO obviously this is not the way it will be...
            key: input.code.0,
        }
    }
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

//TODO instead of Alternative vs OneOf, just have a CaptureGroup pattern
#[derive(Clone)]
pub enum InputPattern {
    Combo(Combo),
    Capture(String, Box<InputPattern>),
    Alternative(Vec<InputPattern>),
    Sequence(Vec<InputPattern>),
    Repeat(Repetition, Box<InputPattern>),
}

// TODO yeet this, this is bad and wrong, because missing backtracking
impl InputPattern {
    pub fn parse(
        &self,
        inputs: &mut Peekable<impl Iterator<Item = KeyInput>>,
    ) -> Option<InputMatch> {
        match self {
            InputPattern::Combo(c) => {
                if c.matches(inputs.peek()?) {
                    Some(InputMatch::KeyInput(inputs.next().unwrap()))
                } else {
                    None
                }
            },
            InputPattern::Alternative(options) => options
                .iter()
                .find_map(|pat| pat.parse(inputs))
                .map(|m| InputMatch::Alternative(Box::new(m))),
            InputPattern::Sequence(elems) => elems
                .iter()
                .map(|pat| pat.parse(inputs))
                .collect::<Option<Vec<InputMatch>>>()
                .map(|entries| InputMatch::Sequence(entries.into_iter().collect())),
            InputPattern::Repeat(rep, pat) => match rep {
                Repetition::Optional => Some(InputMatch::Sequence(
                    pat.parse(inputs).map(|x| vec![x]).unwrap_or_default(),
                )),
                Repetition::ZeroOrMore => {
                    let res = iter::from_fn(|| pat.parse(inputs)).collect();
                    Some(InputMatch::Sequence(res))
                },
                Repetition::OneOrMore => {
                    let res: Vec<_> = iter::from_fn(|| pat.parse(inputs)).collect();
                    (!res.is_empty()).then_some(InputMatch::Sequence(res))
                },
            },
            InputPattern::Capture(name, pat) => Some(InputMatch::Capture(
                name.to_string(),
                Box::new(pat.parse(inputs)?),
            )),
        }
    }
}

#[derive(Clone, Debug)]
pub enum InputMatch {
    KeyInput(KeyInput),
    Capture(String, Box<InputMatch>),
    Alternative(Box<InputMatch>),
    Sequence(Vec<InputMatch>),
}

impl InputMatch {
    fn unwrap_key_input(&self) -> &KeyInput {
        let Self::KeyInput(x) = self else { panic!("{self:?} was not a KeyInput") };
        x
    }
    fn unwrap_alt(&self) -> &InputMatch {
        let Self::Alternative(x) = self else { panic!("{self:?} was not an Alternative") };
        x
    }
    fn unwrap_seq(&self) -> &Vec<InputMatch> {
        let Self::Sequence(x) = self else { panic!("{self:?} was not a Sequence") };
        x
    }
    fn unwrap_capture(&self) -> (&str, &InputMatch) {
        let Self::Capture(x, x1) = self else { panic!("{self:?} was not a Capture") };
        (x, x1)
    }
}

impl std::fmt::Debug for InputPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Combo(arg0) => f.debug_tuple("KeyInput").field(arg0).finish(),
            Self::Alternative(arg0) => f.debug_tuple("Alternative").field(arg0).finish(),
            Self::Sequence(arg0) => f.debug_tuple("Sequence").field(arg0).finish(),
            Self::Repeat(arg0, arg1) => f.debug_tuple("Repeat").field(arg0).field(arg1).finish(),
            Self::Capture(arg0, arg1) => f.debug_tuple("Capture").field(arg0).field(arg1).finish(),
        }
    }
}

pub fn key(k: &str) -> InputPattern {
    InputPattern::Combo(Combo::from_key(k))
}

macro_rules! alt {
    ($($name:literal => $pat:expr),*$(,)?) => {
        InputPattern::Alternative(vec![$(InputPattern::Capture($name.to_string(), Box::new($pat))),*])
    }
}
macro_rules! seq {
    ($($name:literal => $pat:expr),*$(,)?) => {
        InputPattern::Sequence(vec![$(InputPattern::Capture($name.to_string(), Box::new($pat))),*])
    }
}
pub fn many1(x: InputPattern) -> InputPattern {
    InputPattern::Repeat(Repetition::OneOrMore, Box::new(x))
}
pub fn opt(x: InputPattern) -> InputPattern {
    InputPattern::Repeat(Repetition::Optional, Box::new(x))
}

fn digit() -> InputPattern {
    InputPattern::Alternative((0..10).map(|x| key(&x.to_string())).collect())
}

fn input() -> Vec<KeyInput> {
    vec![
        KeyInput {
            modifiers: Modifiers::empty(),
            key: Key("d".to_string()),
            code: RawKey("d".to_string()),
        },
        KeyInput {
            modifiers: Modifiers::empty(),
            key: Key("2".to_string()),
            code: RawKey("2".to_string()),
        },
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
    let digit = InputPattern::Alternative((0..2).map(|x| key(&x.to_string())).collect());
    let number = many1(digit);
    let motion = alt!["next_word" => key("w"), "prev_word" => key("b")];
    let repeated_motion = seq!["count" => opt(number), "motion" => motion];
    let verb = alt!["delete" => key("d"), "change" => key("c")];
    let action = seq!["verb" => verb, "motion" => repeated_motion.clone()];
    alt!["action" => action, "motion" => repeated_motion]
}

#[test]
fn graphviz_lol() {
    let digit = InputPattern::Alternative((0..2).map(|x| key(&x.to_string())).collect());
    let number = many1(digit);
    let motion = alt!["next_word" => key("w"), "prev_word" => key("b")];
    let repeated_motion = seq!["count" => opt(number.clone()), "motion" => motion];
    let verb = alt!["delete" => key("d"), "change" => key("c")];
    let action = seq!["verb" => verb, "motion" => repeated_motion.clone()];
    let keymap = alt!["action" => action, "motion" => repeated_motion.clone()];

    let mut nfa = Nfa::from_input_pattern(keymap);
    //nfa.simplify();
    //nfa.simplify();
    //nfa.simplify();
    //nfa.simplify();
    //nfa.simplify();

    println!("{}", nfa.to_graphviz());

    println!("{}", nfa.test(&input()));

    panic!()
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
        m.unwrap_seq()
            .iter()
            .flat_map(|x| x.unwrap_seq().iter())
            .map(|x| x.unwrap_key_input().key.as_str())
            .join("")
            .parse::<usize>()
            .unwrap()
    }

    fn interpret_repeated_motion(m: &InputMatch) -> (usize, Motion) {
        let m = m.unwrap_seq();
        let m: HashMap<_, _> = m.iter().map(|x| x.unwrap_capture()).collect();
        let count = interpret_number(m["count"]);
        let motion = match m["motion"].unwrap_alt().unwrap_capture().0 {
            "next_word" => Motion::NextWord,
            "prev_word" => Motion::PrevWord,
            _ => unreachable!(),
        };
        (count, motion)
    }

    fn interpret_verb(m: &InputMatch) -> Verb {
        match m.unwrap_alt().unwrap_capture().0 {
            "delete" => Verb::Delete,
            "change" => Verb::Change,
            _ => unreachable!(),
        }
    }

    let alternative = res.unwrap_alt().unwrap_capture();
    match alternative.0 {
        "action" => {
            let s = alternative.1.unwrap_seq();
            let s: HashMap<_, _> = s.iter().map(|x| x.unwrap_capture()).collect();
            let verb = interpret_verb(s["verb"]);
            let motion = interpret_repeated_motion(s["motion"]);
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
