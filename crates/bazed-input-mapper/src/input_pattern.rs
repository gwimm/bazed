#![allow(unused)]
use std::{
    collections::HashMap,
    iter::{self, Peekable},
    ops::Range,
};

use dyn_clone::DynClone;
use itertools::Itertools;

use crate::{
    input_dfa::ENfa,
    input_event::{Key, KeyInput, Modifiers, RawKey},
};

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
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

pub fn fuck() {
    let enfa = ENfa::from_input_pattern(InputPattern::Combo(Combo::from_key("a")));
    _ = enfa.to_graphviz();
    let nfa = enfa.remove_epsilons();
    nfa.test(&[]);
    _ = nfa.to_graphviz();
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
    let repeated_motion = seq!["count" => opt(number), "motion" => motion];
    let verb = alt!["delete" => key("d"), "change" => key("c")];
    let action = seq!["verb" => verb, "motion" => repeated_motion.clone()];
    let keymap = alt!["action" => action, "motion" => repeated_motion.clone()];

    //let mut nfa = ENfa::from_input_pattern(keymap);
    let mut nfa = ENfa::from_input_pattern(repeated_motion);

    println!(
        "https://dreampuf.github.io/GraphvizOnline/#{}",
        urlencoding::encode(&nfa.to_graphviz())
    );
    let mut nfa = nfa.remove_epsilons();
    nfa.remove_dead_ends();
    println!(
        "https://dreampuf.github.io/GraphvizOnline/#{}",
        urlencoding::encode(&nfa.to_graphviz())
    );
    nfa.simplify();

    println!(
        "https://dreampuf.github.io/GraphvizOnline/#{}",
        urlencoding::encode(&nfa.to_graphviz())
    );

    //println!("{}", nfa.test(&input()));

    panic!()
}

#[test]
fn test_foo() {
    let pattern = foo();
    let input = input();

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
    panic!()
}
