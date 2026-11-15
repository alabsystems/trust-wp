//@ expect: reject
//@ mechanism: local `crate::core::option::Option::unwrap` prints like core's; unwrap spec chosen by path
//@ accept-means: a local lookalike unwrap received core's contract (real result 7)
//@ verdict: error
//@ refused-with: local item `crate::core` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod core { pub mod option {
    pub enum Option<T> { None, Some(T) }
    impl Option<u32> { pub fn unwrap(self) -> u32 { 7 } }
} }
#[ensures(result@ == 1)]
pub fn u() -> u32 { crate::core::option::Option::Some(1u32).unwrap() }
