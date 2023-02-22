use std::{
    cmp,
    collections::{VecDeque, HashMap},
    fmt::{self, Debug, Formatter},
    sync::atomic::{self, AtomicUsize},
};

use extend::ext;

#[ext]
pub(crate) impl<T> VecDeque<T> {
    fn extend_back<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push_back(item)
        }
    }
}

type IntoIter<I/*: IntoIterator*/> = <I as IntoIterator>::IntoIter;
type Item<I/*: Iterator*/> = <I as Iterator>::Item;

#[ext]
pub(crate) impl<Iter: Iterator> Iter {
    fn reversed(self) -> IntoIter<Vec<Item<Iter>>> {
        self.collect::<Vec<_>>().reversed().into_iter()
    }

 // fn sorted_unstable_by<F>(self, compare: F) -> IntoIter<Vec<Item<Iter>>>
 // where F: for<'a, 'b> FnMut(&'a Item<Iter>, &'b Item<Iter>) -> cmp::Ordering {
 //     self.collect::<Vec<_>>()
 //         .sorted_unstable_by(compare)
 //         .into_iter()
 // }
}

#[ext(name = VecExt)]
pub(crate) impl<T> Vec<T> {
    fn reversed(mut self) -> Self {
        self.reverse();
        self
    }

    fn sorted_unstable_by<F>(mut self, compare: F) -> Self
    where
        F: for<'a, 'b> FnMut(&'a T, &'b T) -> cmp::Ordering,
    {
        self.sort_unstable_by(compare);
        self
    }
}

#[ext(name = HashMapExt)]
pub(crate) impl<K, V> HashMap<K, V> {
    fn filter<F>(&mut self, mut f: F)
    where F: FnMut(&K, &mut V) -> bool {
        self.retain(|k, v| !f(k, v));
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Hash, derive_more::Display, PartialOrd, Ord)]
pub struct Id(pub(crate) usize);

impl Debug for Id {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl Id {
    pub(crate) fn gen() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self(COUNTER.fetch_add(1, atomic::Ordering::SeqCst))
    }
}
