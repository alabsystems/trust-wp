//@ expect: reject
//@ mechanism: Iterator::collect spec — an ungated collect clause must not reach (or crash on) a String target
//@ fixed-by: wp-s24 (ITERATOR_COLLECT split into gated ITERATOR_COLLECT_ROUNDTRIP)
//@ accept-means: the collect spec made the program state inconsistent (a vacuous premise). Refuting execution: any two &str pieces collect to a String and execution reaches the assertion.
//@ teeth: Before the fix the ungated `result.from_iter_post(self@)` clause crashed ay while declaring `method_from_iter_post_2_..String..Seq` ("registered without a unique core declaration identity"), so this case ended in a solver panic rather than a verdict. After it the generic collect spec carries no clause and the assertion is refuted cleanly. The body avoids `s@.len()`: String/str view `len` hits a separate, collect-independent ay declaration panic (reproduces on `proof_assert!(s@.len() == 2)` with no collect).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 2)]
pub fn string_bad(v: Vec<&str>) {
    let _s: String = v.into_iter().collect();
    proof_assert!(false);
}
