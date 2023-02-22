#![feature(once_cell)]
#![feature(let_chains)]
#![feature(hash_drain_filter)]
#![feature(extend_one)]
#![forbid(unreachable_pub)]
#![deny(rustdoc::broken_intra_doc_links)]
#![allow(rustdoc::private_intra_doc_links)]
#![feature(box_patterns)]
#![feature(iter_intersperse)]
//! An acceptor, also known as an atomaton

mod common;
pub mod enfa;
pub mod nfa;
pub mod regex;
pub mod tdfa;
pub mod tenfa;
