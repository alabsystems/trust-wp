//@ expect: reject
//@ mechanism: local `crate::std::mem::swap` no-op prints `std::mem::swap`
//@ accept-means: a local no-op received std::mem::swap's contract
//@ verdict: error
//@ refused-with: local item `crate::std` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod std { pub mod mem { pub fn swap<T>(_a: &mut T, _b: &mut T) {} } }
#[ensures(result@ == 2)]
pub fn s() -> u32 { let mut a = 1u32; let mut b = 2u32; crate::std::mem::swap(&mut a, &mut b); a }
