//!
//! Library crate for lambda_calc, a lambda calculus interpreter.
//!
//! This crate contains the lexer and parser, along with methods for printing
//! and beta reducing the resulting expressions.
//!

pub mod lexer;
pub mod parser;
pub mod ast;

pub use parser::Parser;
pub use ast::{Ast, Expr};
