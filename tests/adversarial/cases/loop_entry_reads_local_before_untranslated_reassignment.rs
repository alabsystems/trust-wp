//@ expect: reject
//@ mechanism: the walk that states a loop invariant at loop entry reads a local at the value it held before an
//@ mechanism: assignment the translator leaves untranslated: after `let mut a = 0u32; a = x | u32::MAX;` (an
//@ mechanism: associated constant used directly as an operand, which the operator path does not evaluate) or
//@ mechanism: `a = q as usize` (a pointer-to-integer cast), `#[invariant(a == 0u32)]` is established at entry
//@ mechanism: and the loop credits it, and a postcondition that reads the invariant after the loop
//@ mechanism: (`result == 0u32` of a function returning `a`) is credited too. A snapshot taken after the
//@ mechanism: assignment is read the same way, and so is an assignment made on one arm only. A parameter
//@ mechanism: reassigned so before the loop is read at its entry value: the walk records a parameter as
//@ mechanism: written before the loop only on a write it translates. The postcondition walk binds the same
//@ mechanism: assignment to a symbol of its site (D-169) and refuses the claim without the loop; the
//@ mechanism: `proof_assert!` walk's own stale
//@ mechanism: read is assertion_reads_local_before_untranslated_reassignment.rs (RED). The control
//@ mechanism: loop_entry_reads_local_after_translated_reassignment_control.rs is the same shapes with a
//@ mechanism: translated assignment.
//@ accept-means: `preloop_invariant(0, 1)`, `preloop_post(0, 1)` and `snapshot_invariant_then_return(0, 1)`
//@ accept-means: hold `a == u32::MAX` at loop entry and return `u32::MAX`; `preloop_invariant_ptr(q, 1)` holds
//@ accept-means: the address of `q`; `one_arm(0, 1, true)` holds `u32::MAX`; `param_reassigned(0, 1)` returns
//@ accept-means: `u32::MAX`. An accept credits each invariant `== 0` and each `result == 0u32`.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means the loop-entry walk binds an
//@ fixed-by: untranslated assignment as the postcondition walk does (D-169's site symbol), never to the
//@ fixed-by: earlier value.
//@ teeth: every function verified, exit 0, on the campaign tip and with D-217.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unused_assignments)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(n < 10u32)]
pub fn preloop_invariant(x: u32, n: u32) {
    let mut a = 0u32;
    a = x | u32::MAX;
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
}

#[requires(n < 10u32)]
pub fn preloop_invariant_ptr(q: *const u8, n: u32) {
    let mut a = 0usize;
    a = q as usize;
    let mut i = 0u32;
    #[invariant(a == 0usize)]
    while i < n {
        i += 1;
    }
}

#[requires(n < 10u32)]
#[ensures(result == 0u32)]
pub fn preloop_post(x: u32, n: u32) -> u32 {
    let mut a = 0u32;
    a = x | u32::MAX;
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
    a
}

#[requires(n < 10u32)]
#[ensures(result == 0u32)]
pub fn snapshot_invariant_then_return(x: u32, n: u32) -> u32 {
    let mut a = 0u32;
    a = x | u32::MAX;
    let s = snapshot!(a);
    let mut i = 0u32;
    #[invariant(*s == 0u32)]
    #[invariant(a == *s)]
    while i < n {
        i += 1;
    }
    a
}

#[requires(n < 10u32)]
pub fn one_arm(x: u32, n: u32, c: bool) {
    let mut a = 0u32;
    if c {
        a = x | u32::MAX;
    }
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
}

#[requires(x == 0u32)]
#[requires(n < 10u32)]
#[ensures(result == 0u32)]
pub fn param_reassigned(mut x: u32, n: u32) -> u32 {
    x = x | u32::MAX;
    let mut i = 0u32;
    #[invariant(x == 0u32)]
    while i < n {
        i += 1;
    }
    x
}
