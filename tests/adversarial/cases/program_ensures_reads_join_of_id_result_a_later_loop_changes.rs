//@ expect: reject
//@ mechanism: the equality form of program_ensures_reads_join_of_call_result_a_later_loop_changes.rs: `let
//@ mechanism: mut m = id(y)`, `let w = if c { m } else { 200 }`, `let r = id(w)`, a later loop writes `m =
//@ mechanism: 150`, `ensures(result@ >= 100)`. The join definition `c ==> w$walk_join == m` read `m` at the
//@ mechanism: loop's exit.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, true)` returns 5.
//@ also-verified: id, small
//@ fixed-by: D-244 (a call result a later loop may change is named by a symbol of its site in a slice read
//@ fixed-by: after that loop, and every premise of the dependency closure, a join definition included, is
//@ fixed-by: retired where it reads a name a later loop may change)
//@ teeth: ACCEPTED at exit 0 with D-243; `failed` with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == y)]
pub fn id(y: u32) -> u32 { y }

#[ensures(result@ < 10)]
pub fn small(y: u32) -> u32 { if y < 10 { y } else { 0 } }

#[ensures(result@ >= 100)]
pub fn go(y: u32, c: bool) -> u32 {
    let mut m = id(y);
    let w = if c { m } else { 200u32 };
    let r = id(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ >= 100))]
    while i < 3 {
        m = 150;
        i += 1;
    }
    r
}
