//@ expect: verify
//@ mechanism: control for sp11 — the real spec-library Seq::len in logic must still be recognised
//@ accept-means: n/a (control)
use creusot_std::prelude::*;
#[logic(open)]
#[ensures(result >= 0)]
pub fn g(s: Seq<u32>) -> Int { s.len() }
