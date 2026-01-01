#![feature(never_type, box_into_inner, if_let_guard, try_trait_v2, assert_matches)]
#![allow(clippy::new_without_default)]

pub mod id;
pub mod text_span;
pub mod maybe_result;
pub mod error;
pub mod stage;
pub mod ast;
pub mod parse;
pub mod symbols;
pub mod types;
// pub mod cps;
// pub mod codegen;
