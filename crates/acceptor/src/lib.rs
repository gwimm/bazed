#![feature(once_cell)]
#![feature(let_chains)]
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
pub mod tenfa;
