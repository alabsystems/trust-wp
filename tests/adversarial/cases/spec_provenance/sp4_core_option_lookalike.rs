//@ expect: reject
//@ mechanism: local `crate::core::option::Option::is_some` prints like core's
//@ accept-means: a local lookalike Option received core Option::is_some's contract (real false)
//@ verdict: error
//@ refused-with: local item `crate::core` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod core { pub mod option {
    pub enum Option<T> { None, Some(T) }
    impl<T> Option<T> { pub fn is_some(&self) -> bool { false } }
} }
#[ensures(result == true)]
pub fn o() -> bool { let x = crate::core::option::Option::Some(1u32); x.is_some() }
