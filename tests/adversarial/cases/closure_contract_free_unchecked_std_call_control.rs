//@ expect: verify
//@ xfail: a contract-free closure is a verification target of nothing, so a call entering it is
//@ xfail: unaccounted whatever the argument and `f` stays `unknown (partial: panic paths
//@ xfail: unchecked (call to std::ops::Fn::call))`. Retiring it needs the closure's own panic
//@ xfail: paths checked by some lane, not a wider credit at the call.
//@ mechanism: the TRUE twin of closure_contract_free_unchecked_std_call_unaccounted, identical but
//@ mechanism: for the length asked for, far below a zero-sized vector's capacity. It is the price of
//@ mechanism: D-103's soundness half, committed so that an XPASS here with the RED twin still
//@ mechanism: rejecting is the signal that contract-free closures became checked targets.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — measured `unknown`, the same verdict as its RED twin, on the binary that
//@ teeth: separates the spec-bearing pairs beside it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = |n: usize| -> usize {
        let mut v: Vec<()> = vec![(); n];
        v.push(());
        v.len()
    };
    let _r = c(8);
}
