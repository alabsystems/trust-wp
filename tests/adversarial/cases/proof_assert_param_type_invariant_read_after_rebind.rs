//@ expect: reject
//@ mechanism: a BY-VALUE parameter of a type with an invariant, re-bound or written by a plain write,
//@ mechanism: then a `proof_assert!` of the invariant: `p = P(any(), 1)` under a contract, the same in a
//@ mechanism: contract-free host, and `p.0 = any()`, each followed by `proof_assert!(p.0@ > 0)` where
//@ mechanism: `P`'s invariant is `self.0@ > 0`. D-140 withdraws a re-bound parameter's `#[requires]`
//@ mechanism: facts from the assertion's premises (`rebound_param_names`, `drop_stale_param_facts`), and
//@ mechanism: D-38 a loop-invalidated one's; the lane then injects the type invariant of every parameter
//@ mechanism: the assertion names (`build_type_invariant_clauses`) without asking either list. That
//@ mechanism: `inv(p)` is a fact about the ENTRY value under the parameter's name, and it sits beside the
//@ mechanism: substitution fact `p == P(r, 1)`, so it gives `r > 0`: the premises the proof uses are
//@ mechanism: `true`, `inv(p)` and `p == P($call, 1)`. The same assertion over a type with no invariant is
//@ mechanism: FAILED, and its `#[requires(p.0@ > 0)]` twin over such a type is FAILED at D-140's head (the
//@ mechanism: plain-write withdrawal) and verified on the campaign driver it branches from. The hand-off
//@ mechanism: spelling (`{ let _g = G(&mut p.0); }` with a `Drop` storing 0) is `unknown` at D-140's head,
//@ mechanism: refused by the self-check, and verified on the campaign driver. Found probing D-140's
//@ mechanism: withdrawal sideways; the loop spelling is proof_assert_param_type_invariant_read_after_loop_rebind.
//@ accept-means: a `proof_assert!` is credited from a by-value parameter's entry type invariant after the
//@ accept-means: body overwrote the parameter with a value the invariant says nothing about, and the crate
//@ accept-means: exits 0.
//@ WHY THE CONTRACT IS FALSE: `any` returns 0, so at each assertion `p.0` is 0 and `p.0@ > 0` is false.
//@ WHY THE CONTRACT IS FALSE: Creusot assumes a parameter's invariant at entry only; a value the body
//@ WHY THE CONTRACT IS FALSE: builds or writes owes its invariant at the next boundary and gives none before.
//@ fixed-by: D-241: a written parameter's injected type invariant speaks of its entry symbol, or is withdrawn with its `#[requires]` where the write cannot be versioned, never of its value at the assertion.
//@ teeth: LIVE: ACCEPTED, exit 0, each `proof_assert in creusot_test::<fn> verified` and each function
//@ teeth: `verified`, on D-140's driver and on the campaign driver it branches from, so not a regression.
//@ teeth: Control: proof_assert_param_type_invariant_rebind_control (the invariant at entry, and after a
//@ teeth: re-bind or write of a value that satisfies it), verified on both.
//@ also-verified: any
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct P(pub u32, pub u32);

impl Invariant for P {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ > 0 }
    }
}

#[requires(true)]
#[ensures(true)]
pub fn any() -> u32 {
    0
}

#[requires(true)]
pub fn rebind(mut p: P) {
    p = P(any(), 1);
    proof_assert!(p.0@ > 0);
    let _ = p;
}

pub fn rebind_contract_free(mut p: P) {
    p = P(any(), 1);
    proof_assert!(p.0@ > 0);
}

#[requires(true)]
pub fn field_write(mut p: P) {
    p.0 = any();
    proof_assert!(p.0@ > 0);
    let _ = p;
}
