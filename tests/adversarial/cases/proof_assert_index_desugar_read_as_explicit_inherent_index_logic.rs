//@ expect: reject
//@ mechanism: The assertion spelling of ensures_index_desugar_read_as_explicit_inherent_index_logic.rs:
//@ mechanism: `s[0]` is lowered to the same term as the explicit `s.index_logic(0)`, which Rust reads as
//@ mechanism: the inherent method, and the assertion is credited with no solver query.
//@ accept-means: an assertion equating two different logic functions' values is credited with no query.
//@ WHY IT IS FALSE: `s[0]` is `2` and `s.index_logic(0)` is `1`, so the assertion is `false`.
//@ teeth: MEASURED ACCEPTED, exit 0 (`proof_assert in creusot_test::prog verified ✓`, no solver query) with
//@ teeth: D-163 and D-164 in force, and at the campaign tip.
//@ fixed-by: OPEN — committed RED rather than hidden (see the ensures spelling).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::logic::ops::IndexLogic;
use creusot_std::prelude::*;

pub struct S;

impl S {
    #[logic(open)]
    pub fn index_logic(self, i: Int) -> Int {
        1
    }
}

impl IndexLogic<Int> for S {
    type Item = Int;
    #[logic(open)]
    fn index_logic(self, i: Int) -> Int {
        2
    }
}

pub fn prog(s: S) {
    proof_assert!(s[0] == s.index_logic(0));
}
