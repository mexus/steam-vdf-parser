//! Core data structures for VDF representation.

mod impls;
mod types;

#[cfg(test)]
mod tests;

pub use types::{Obj, Value, Vdf};
