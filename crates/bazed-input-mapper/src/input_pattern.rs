use std::ops::Range;

use dyn_clone::DynClone;

use crate::input_event::{KeyInput, Modifiers};

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
}

#[derive(Debug, Clone)]
pub enum Repetition {
    Optional,
    ZeroOrMore,
    OneOrMore,
    Range(Range<usize>),
}

pub trait KeyPredicate: DynClone {
    fn check(&self, input: KeyInput) -> bool;
}
dyn_clone::clone_trait_object!(KeyPredicate);

#[derive(Clone)]
pub enum InputPattern {
    KeyInput(Combo),
    CheckFn(Box<dyn KeyPredicate + 'static>),
    Named(String, Box<InputPattern>),
    Alternative(Vec<InputPattern>),
    Sequence(Vec<InputPattern>),
    Repeat(Repetition, Box<InputPattern>),
}

impl std::fmt::Debug for InputPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::KeyInput(arg0) => f.debug_tuple("KeyInput").field(arg0).finish(),
            Self::CheckFn(_) => f.debug_tuple("CheckFn").finish(),
            Self::Named(arg0, arg1) => f.debug_tuple("Named").field(arg0).field(arg1).finish(),
            Self::Alternative(arg0) => f.debug_tuple("Alternative").field(arg0).finish(),
            Self::Sequence(arg0) => f.debug_tuple("Sequence").field(arg0).finish(),
            Self::Repeat(arg0, arg1) => f.debug_tuple("Repeat").field(arg0).field(arg1).finish(),
        }
    }
}

pub fn key(k: &str) -> InputPattern {
    InputPattern::KeyInput(Combo::from_key(k))
}
pub fn named(n: &str, p: InputPattern) -> InputPattern {
    InputPattern::Named(n.to_string(), Box::new(p))
}
pub fn alt(v: Vec<InputPattern>) -> InputPattern {
    InputPattern::Alternative(v)
}
pub fn seq(v: Vec<InputPattern>) -> InputPattern {
    InputPattern::Sequence(v)
}
pub fn many1(x: InputPattern) -> InputPattern {
    InputPattern::Repeat(Repetition::OneOrMore, Box::new(x))
}
pub fn opt(x: InputPattern) -> InputPattern {
    InputPattern::Repeat(Repetition::Optional, Box::new(x))
}

fn foo() {
    let digit = alt((0..10).map(|x| key(&x.to_string())).collect());
    let number = named("number", many1(digit));
    let next_word = named("next_word", key("w"));
    let prev_word = named("next_word", key("b"));
    let motion = named("motion", alt(vec![next_word, prev_word]));
    let repeated_motion = named("motion", seq(vec![opt(number), motion]));
    let change = named("change", key("c"));
    let delete = named("delete", key("d"));
    let verb = named("verb", alt(vec![delete, change]));
    let action = named("action", seq(vec![verb, repeated_motion.clone()]));
    let keymap = named("keymap", alt(vec![action, repeated_motion]));
}


