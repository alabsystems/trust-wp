//@ expect: reject
//@ mechanism: local `crate::core::cmp::max` prints `core::cmp::max`; the std max spec was chosen by printed path
//@ accept-means: a local lookalike received core::cmp::max's contract (real result 3)
//@ verdict: error
//@ refused-with: local item `crate::core` shadows a standard or spec-library path root
//@ teeth-credit: wp-s47 v2 — credited only as this named trust-wp output (the reserved-root backstop refuses the crate before any spec lookup); measured at edition 2024.
use creusot_std::prelude::*;
pub mod core { pub mod cmp { pub fn max<T>(a: T, _b: T) -> T { a } } }
#[ensures(result@ == 5)]
pub fn m() -> u32 { crate::core::cmp::max(3u32, 5u32) }
