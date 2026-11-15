//@ expect: verify
//@ mechanism: Iterator::collect spec — the `result@ == self@` view bridge must not reach non-roundtrip collects
//@ fixed-by: wp-s24 (ITERATOR_COLLECT split into gated ITERATOR_COLLECT_ROUNDTRIP)
//@ accept-means: n/a (control) — this contract is TRUE; it must verify via the gated roundtrip spec.
//@ mechanism: It also needs `Vec::into_iter` to state Creusot's own `self@ == result@`. Stated as
//@ mechanism: `result@.ext_eq(self@)`, the premise carried a pointwise quantifier the base
//@ mechanism: vacuity recheck could not decide, and the run ended at the watchdog as a timeout.
//@ teeth: n/a — over-refusal control for the (Self, B) whitelist; h_collect_roundtrip_vec_len is
//@ teeth: its false twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 3)]
#[ensures(result@.len() == 3)]
pub fn c_ok(v: Vec<u32>) -> Vec<u32> {
    let r: Vec<u32> = v.into_iter().collect();
    r
}
