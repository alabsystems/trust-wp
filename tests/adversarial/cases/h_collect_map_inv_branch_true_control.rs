//@ expect: verify
//@ xfail: not provable today for reasons outside collect. Its collect-free twin (`if b { mk() } else { Vec::new() }`, mk ensures len == 1) is vacuous: every call postcondition about the shared return slot call_0 is a whole-function assumption. Here the collect facts are per-call-site, so the b-branch no longer contradicts, but the !b slice still FAILS: result = ite(b, call_0_collect_bbN, call_0) and call_0's view (Uninterpreted Seq) does not reach result_view (Seq(Int)). It was vacuous on 51cca4a.
//@ mechanism: map_inv collect view facts — must be about a per-call-site symbol, never about call_<dest> shared across paths
//@ fixed-by: wp-s24 (collect-hardening-v2)
//@ accept-means: n/a (control) — TRUE per-branch lengths; must verify, not vacuous.
//@ teeth: Review of 51cca4a: vacuous (contradictory premises): the collect facts about call_0 contradicted the else branch's Vec::new.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// TRUE contract: on b the Vec has 3 elements, otherwise 0.
#[ensures(b ==> result@.len() == 3)]
#[ensures(!b ==> result@.len() == 0)]
pub fn ctrl(b: bool) -> Vec<u32> {
    if b {
        (0u32..3).map_inv(|x, _| x).collect()
    } else {
        Vec::new()
    }
}
