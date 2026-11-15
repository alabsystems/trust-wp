//@ expect: reject
//@ mechanism: local `crate::core::panicking::panic` returns normally; recognising it as a panic entry point turns the arm into an assumption
//@ accept-means: a normally-returning local fn was treated as a core panic
//@ verdict: error
//@ refused-with: local item `crate::core` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod core { pub mod panicking { pub fn panic(_msg: &str) {} } }
#[ensures(result@ == 1)]
pub fn p(x: u32) -> u32 { if x != 1 { crate::core::panicking::panic("no") } x }
