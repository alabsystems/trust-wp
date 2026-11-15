//@ expect: reject
//@ mechanism: an impl the run never examined counts as having discharged the trait contract it
//@ mechanism: owes. The trait-credit ledger records an undischarged contract only on positive
//@ mechanism: evidence (the impl FAILED, errored, panicked, was assumed), and the #3771 adaptive
//@ mechanism: fail-fast stop abandons every contract behind the first validated failure. Here
//@ mechanism: `bad` fails, the stop fires before `<W as Rd>::rd`'s body is verified, the
//@ mechanism: refinement pass sees a verbatim restatement of the trait's clauses and has nothing
//@ mechanism: to refute, so `Rd::rd` is never recorded undischarged and `gen_read` and `go` keep
//@ mechanism: their credits although the only impl returns false. The stop is reachable in
//@ mechanism: ordinary runs: at the compat lane's per-row wall a crate oversubscribes the adaptive
//@ mechanism: budget with a modest number of contracted functions, and one validated failure then
//@ mechanism: stops it.
//@ fixed-by: D-94 (implementations of contracted trait methods are verified after the adaptive stop)
//@ accept-means: `go` claims `result` and returns false; `gen_read` holds a trait grant whose only impl was never examined.
//@ teeth: MEASURED on the call-graph withdrawal walk alone: `gen_read verified ✓`, `go verified ✓`, `bad FAILED`, then `stopping remaining contract verification after first adaptive-budget VALIDATED failure`, and no withdrawal line. The same crate with `bad` returning 2 is examined in full: `<W as Rd>::rd FAILED` and both credits are withdrawn, so the stop alone is what keeps them. Its isolating twin trait_impl_unexamined_after_fail_fast_stop_discharged_twin.rs (the impl returns true) keeps both.
//@ note: the fillers make the crate oversubscribe the adaptive budget at this wall; their credits are TRUE.
//@ timeout: 300
//@ also-verified: f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    gen_read::<W>(&W)
}

// A validated failure: under an oversubscribed adaptive budget it stops the run.
#[ensures(result == 2u32)]
pub fn bad() -> u32 {
    1
}

#[ensures(result == 0u32)]
pub fn f0() -> u32 {
    0
}

#[ensures(result == 1u32)]
pub fn f1() -> u32 {
    1
}

#[ensures(result == 2u32)]
pub fn f2() -> u32 {
    2
}

#[ensures(result == 3u32)]
pub fn f3() -> u32 {
    3
}

#[ensures(result == 4u32)]
pub fn f4() -> u32 {
    4
}

#[ensures(result == 5u32)]
pub fn f5() -> u32 {
    5
}

#[ensures(result == 6u32)]
pub fn f6() -> u32 {
    6
}

#[ensures(result == 7u32)]
pub fn f7() -> u32 {
    7
}

#[ensures(result == 8u32)]
pub fn f8() -> u32 {
    8
}

#[ensures(result == 9u32)]
pub fn f9() -> u32 {
    9
}

#[ensures(result == 10u32)]
pub fn f10() -> u32 {
    10
}

#[ensures(result == 11u32)]
pub fn f11() -> u32 {
    11
}

// Restates the trait's clause, so its refinement goal is a tautology and the
// body is the only obligation that could find the `false`; the stop skips it.
impl Rd for W {
    #[ensures(result)]
    fn rd(&self) -> bool {
        false
    }
}
