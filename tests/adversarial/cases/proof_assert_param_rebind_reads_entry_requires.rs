//@ expect: reject
//@ mechanism: a BY-VALUE parameter the body re-binds by a plain write to a value that does not contradict
//@ mechanism: its precondition, then a `proof_assert!`: `x = y; proof_assert!(x@ == 0)` and
//@ mechanism: `x = y; proof_assert!(y@ == 0)` under `#[requires(x@ == 0)]`, `x = any()` (a verified callee
//@ mechanism: whose result nothing constrains), and `x = j` after a loop. The proof_assert lane equates the
//@ mechanism: parameter's name with its binding at the assertion (`x == y`) and reads the precondition, a fact
//@ mechanism: about the ENTRY value under the same name, beside it, so the entry fact constrains `y`, the
//@ mechanism: call's result or `j`. After the loop the precondition also comes back as a loop-exit fact the
//@ mechanism: loop lane carried across the loop (`x@ == 0`), read through the assertion's substitution as
//@ mechanism: `j@ == 0`. A write the precondition contradicts (`x = 7`) collides with it and is refused as a
//@ mechanism: vacuous proof instead; drop glue writing the parameter is
//@ mechanism: proof_assert_entry_requires_pins_param_after_drop_glue. Found probing D-140's hand-off
//@ mechanism: withdrawal sideways; no drop is involved.
//@ accept-means: a `proof_assert!` is credited from a parameter's entry precondition after the body
//@ accept-means: re-bound the parameter to a value the precondition says nothing about, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: at each assertion the asserted value is `y`, `j` or 9 (what `any` returns);
//@ WHY THE CONTRACT IS FALSE: the precondition says only that `x` was 0 at entry.
//@ fixed-by: D-140: the proof_assert lane withdraws the entry facts, and the loop-exit facts, naming a
//@ fixed-by: by-value parameter its substitution re-binds.
//@ teeth: MEASURED on one binary with the withdrawal disabled by an env knob (never committed): each
//@ teeth: function ACCEPTED, exit 0, each `proof_assert in creusot_test::<fn> verified`; with it, each
//@ teeth: assertion is FAILED. Control: proof_assert_param_rebind_keeps_other_entry_facts_control.
//@ also-verified: any
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn alias_self(mut x: u32, y: u32) {
    x = y;
    proof_assert!(x@ == 0);
}

#[requires(x@ == 0)]
pub fn alias_other(mut x: u32, y: u32) {
    x = y;
    proof_assert!(y@ == 0);
    let _ = x;
}

#[requires(true)]
#[ensures(true)]
pub fn any() -> u32 {
    9
}

#[requires(x@ == 0)]
pub fn from_callee(mut x: u32) {
    x = any();
    proof_assert!(x@ == 0);
}

#[requires(x@ == 0)]
pub fn after_loop(mut x: u32, j: u32) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    x = j;
    proof_assert!(j@ == 0);
    let _ = x;
}
