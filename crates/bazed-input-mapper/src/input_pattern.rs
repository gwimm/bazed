#![allow(unused)]
use std::{
    collections::HashMap,
    iter::{self, Peekable},
    ops::Range,
};

use dyn_clone::DynClone;
use itertools::Itertools;

use crate::input_event::{Key, KeyInput, Modifiers, RawKey};

#[derive(Debug, Clone)]
pub struct Combo {
    modifiers: Modifiers,
    key: String,
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
    KeyInput(Combo),
    CheckFn(Box<dyn KeyPredicate + 'static>),
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
            InputPattern::KeyInput(c) => {
                if c.matches(inputs.peek()?) {
                    let k = inputs.next().unwrap();
                    Some(InputMatch::KeyInput(k))
                } else {
                    None
                }
            },
            InputPattern::CheckFn(f) => {
                if f.check(inputs.peek()?) {
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

#[derive(Clone, Debug, derive_more::Unwrap)]
pub enum InputMatch {
    KeyInput(KeyInput),
    Alternative(String, Box<InputMatch>),
    List(Vec<InputMatch>),
    Sequence(HashMap<String, InputMatch>),
}

impl std::fmt::Debug for InputPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::KeyInput(arg0) => f.debug_tuple("KeyInput").field(arg0).finish(),
            Self::CheckFn(_) => f.debug_tuple("CheckFn").finish(),
            Self::Alternative(arg0) => f.debug_tuple("Alternative").field(arg0).finish(),
            Self::OneOf(arg0) => f.debug_tuple("OneOf").field(arg0).finish(),
            Self::Sequence(arg0) => f.debug_tuple("Sequence").field(arg0).finish(),
            Self::Repeat(arg0, arg1) => f.debug_tuple("Repeat").field(arg0).field(arg1).finish(),
        }
    }
}

pub fn key(k: &str) -> InputPattern {
    InputPattern::KeyInput(Combo::from_key(k))
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

macro_rules! def_alt {
    ($pat_name:ident = [$($name:ident => $pat:expr => $t:ty),*$(,)?]) => {
        #[derive(Debug)]
        enum $pat_name {
            $($name($t)),*
        }
        impl $pat_name {
            fn input_pattern() -> InputPattern {
                InputPattern::Alternative(
                    vec![$((::std::stringify!($name).to_string(), $pat)),*]
                )
            }
            fn from_match(m: InputMatch) -> Self {
                let InputMatch::Alternative(variant, value) = m else { unreachable!() };
                match variant.as_str() {
                    $(::std::stringify!($name) => Self::$name(<$t>::from_match(*value))),*,
                    _ => unreachable!(),
                }
            }
        }
    }
}

macro_rules! def_seq {
    ($pat_name:ident = [$($name:ident => $pat:expr => $t:ty),*$(,)?]) => {
        #[derive(Debug)]
        struct $pat_name {
            $($name: $t),*
        }
        impl $pat_name {
            fn input_pattern() -> InputPattern {
                InputPattern::Sequence(
                    vec![$((::std::stringify!($name).to_string(), $pat)),*]
                )
            }
            fn from_match(m: InputMatch) -> Self {
                let InputMatch::Sequence(mut entries) = m else { unreachable!() };
                Self {
                    $($name: <$t>::from_match(entries.remove(::std::stringify!($name)).unwrap())),*
                }
            }
        }
    }
}

#[derive(Debug)]
struct PatKey {
    key: KeyInput,
}

impl PatKey {
    fn from_match(m: InputMatch) -> Self {
        let InputMatch::KeyInput(key) = m else { unreachable!() };
        Self { key }
    }
}

macro_rules! def_list {
    ($pat_name:ident = $t:ty) => {
        #[derive(Debug)]
        struct $pat_name {
            entries: Vec<$t>,
        }
        impl $pat_name {
            fn from_match(m: InputMatch) -> Self {
                let InputMatch::List(entries) = m else { unreachable!() };
                Self {
                    entries: entries.into_iter().map(|x| <$t>::from_match(x)).collect(),
                }
            }
        }
    };
}

def_alt!(PatMotion = [
    NextWord => key("w") => PatKey,
    PrevWord => key("b") => PatKey,
]);

def_alt!(PatVerb = [
    Delete => key("d") => PatKey,
    Change => key("c") => PatKey,
]);

fn digit() -> InputPattern {
    InputPattern::OneOf((0..10).map(|x| key(&x.to_string())).collect())
}
def_list!(PatNumber = PatKey);
def_list!(PatOptNumber = PatNumber);

def_seq!(PatRepeatedMotion = [
    count => many1(digit()) => PatOptNumber,
    motion => PatMotion::input_pattern() => PatMotion,
]);

def_seq!(PatAction = [
    verb => PatVerb::input_pattern() => PatVerb,
    motion => PatMotion::input_pattern() => PatRepeatedMotion,
]);

def_alt!(PatKeymap = [
    Motion => PatMotion::input_pattern() => PatRepeatedMotion,
    Action => PatAction::input_pattern() => PatAction,
]);

#[test]
fn bar() {
    let res = PatKeymap::input_pattern()
        .parse(&mut input().into_iter().peekable())
        .unwrap();
    match PatKeymap::from_match(res) {
        PatKeymap::Motion(motion) => {
            let count = motion
                .count
                .entries
                .iter()
                .flat_map(|x| x.entries.iter())
                .map(|x| &x.key.key)
                .join("")
                .parse::<usize>()
                .unwrap();

            match motion.motion {
                PatMotion::NextWord(_) => println!("next by {count}"),
                PatMotion::PrevWord(_) => println!("prev by {count}"),
            };
        },
        PatKeymap::Action(action) => {
            println!("verb: {:?}", action.verb);
            println!("motion: {:?}", action.motion);
        },
    }
    panic!();
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
    let digit = InputPattern::OneOf((0..10).map(|x| key(&x.to_string())).collect());
    let number = many1(digit);
    let motion = alt!["next_word" => key("w"), "prev_word" => key("b")];
    let repeated_motion = seq!["count" => opt(number), "motion" => motion];
    let verb = alt!["delete" => key("d"), "change" => key("c")];
    let action = seq!["verb" => verb, "motion" => repeated_motion.clone()];
    let keymap = alt!["action" => action, "motion" => repeated_motion];
    keymap
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

    fn interpret_repeated_motion(m: InputMatch) -> (usize, Motion) {
        let m = m.unwrap_sequence();
        let count = m.get("count").unwrap().clone();
        let count = count.unwrap_list();
        let count = count
            .into_iter()
            .flat_map(|x| x.unwrap_list().into_iter())
            .map(|x| x.unwrap_key_input().key)
            .join("")
            .parse::<usize>()
            .unwrap();
        let motion = m.get("motion").unwrap().clone().unwrap_alternative().0;
        let motion = match motion.as_str() {
            "next_word" => Motion::NextWord,
            "prev_word" => Motion::PrevWord,
            _ => unreachable!(),
        };
        (count, motion)
    }
    fn interpret_verb(m: InputMatch) -> Verb {
        match m.unwrap_alternative().0.as_str() {
            "delete" => Verb::Delete,
            "change" => Verb::Change,
            _ => unreachable!(),
        }
    }

    let alternative = res.unwrap_alternative();
    match alternative.0.as_str() {
        "action" => {
            let s = alternative.1.unwrap_sequence();
            let verb = interpret_verb(s.get("verb").unwrap().clone());
            let motion = interpret_repeated_motion(s.get("motion").unwrap().clone());
            println!("Action: {verb:?} {motion:?}");
        },
        "motion" => {
            let motion = interpret_repeated_motion(*alternative.1);
            println!("Move: {motion:?}");
        },
        _ => unreachable!(),
    }

    //println!("{:#?}", res);
    panic!();
}
