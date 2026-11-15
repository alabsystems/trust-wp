//@ expect: verify
//@ mechanism: real core::cmp::max keeps its std contract after the provenance gate
//@ accept-means: n/a (control)
use creusot_std::prelude::*;
#[ensures(result@ == 5)]
pub fn m() -> u32 { core::cmp::max(3u32, 5u32) }
