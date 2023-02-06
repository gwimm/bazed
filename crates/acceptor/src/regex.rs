#[derive(Debug, Clone, Copy)]
pub enum Repeat {
    Optional,
    NoneOrMore,
    OneOrMore,
}

#[derive(Clone)]
pub enum Regex<T> {
    Symbol(T),
    Capture(String, Box<Regex<T>>),
    Alternative(Vec<Regex<T>>),
    Sequence(Vec<Regex<T>>),
    Repeat(Repeat, Box<Regex<T>>),
}

// potential borrowed solution eliminating allocations

// #[derive(Clone, Copy)]
// #[allow(non_camel_case_types)]
// pub enum rg<'a, T> {
//     sym(T),
//     capture(&'a str, &'a rg<'a, T>),
//     alternative(&'a rg<'a, T>),
//     sequence(&'a rg<'a, T>),
//     repeat(Repeat, &'a rg<'a, T>),
// }

// impl<'a, T> std::borrow::Borrow<rg<'a, T>> for Regex<T> {
//     fn borrow(&self) -> &rg<'a, T> {
//         match self {
//             Regex::Symbol(sym) => &rg::sym(sym),
//             _ => todo!(),
//         }
//     }
// }

impl<T> std::fmt::Debug for Regex<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Symbol(arg0) => f.debug_tuple("Symbol").field(arg0).finish(),
            Self::Alternative(arg0) => f.debug_tuple("Alternative").field(arg0).finish(),
            Self::Sequence(arg0) => f.debug_tuple("Sequence").field(arg0).finish(),
            Self::Repeat(arg0, arg1) => f.debug_tuple("Repeat").field(arg0).field(arg1).finish(),
            Self::Capture(arg0, arg1) => f.debug_tuple("Capture").field(arg0).field(arg1).finish(),
        }
    }
}

pub fn sym<T>(symbol: T) -> Regex<T> {
    Regex::Symbol(symbol)
}

pub fn alt<T, I: IntoIterator<Item = Regex<T>>>(alts: I) -> Regex<T> {
    Regex::Alternative(alts.into_iter().collect())
}

pub fn seq<T, I: IntoIterator<Item = Regex<T>>>(elements: I) -> Regex<T> {
    Regex::Sequence(elements.into_iter().collect())
}

pub fn many<T>(sub: Regex<T>) -> Regex<T> {
    Regex::Repeat(Repeat::NoneOrMore, Box::new(sub))
}

pub fn many1<T>(sub: Regex<T>) -> Regex<T> {
    Regex::Repeat(Repeat::OneOrMore, Box::new(sub))
}

pub fn opt<T>(sub: Regex<T>) -> Regex<T> {
    Regex::Repeat(Repeat::Optional, Box::new(sub))
}

#[macro_export]
macro_rules! alt {
    ($($name:literal => $pat:expr),*$(,)?) => {
        Regex::alt([$(Regex::Capture($name.to_string(), Box::new($pat))),*])
    }
}

#[macro_export]
macro_rules! seq {
    ($($name:literal => $pat:expr),*$(,)?) => {
        Regex::seq([$(Regex::Capture($name.to_string(), Box::new($pat))),*])
    }
}

pub fn digit() -> Regex<char> {
    alt(('0'..='9').map(|digit| sym(digit)))
}

pub fn digit1() -> Regex<char> {
    alt(('1'..='9').map(|digit| sym(digit)))
}

pub fn number() -> Regex<char> {
    seq([digit1(), many(digit())])
}

pub fn float() -> Regex<char> {
    let number = number();
    let digit = alt(('0'..='9').map(|digit| sym(digit)));
    let sign = alt(['+', '-'].map(sym));
    seq([opt(sign), seq([number, sym('.')]), many(digit)])
}
