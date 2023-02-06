use std::{
    sync::atomic::{AtomicUsize, Ordering},
    fmt::{self, Debug, Formatter},
};

#[derive(Clone, Copy, Eq, PartialEq, Hash, derive_more::Display, PartialOrd, Ord)]
pub struct Id(usize);

impl Debug for Id {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl Id {
    pub(crate) fn gen() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}
