//@ expect: reject
//@ mechanism: a fn pointer assigned BEFORE an unannotated loop and called INSIDE it was credited by the whole-body resolver while the drop-glue gate's BLOCK-LOCAL resolver saw nothing, so the callee's postcondition was assumed at a site owing no obligation
//@ fixed-by: wp-s62 v2 (resolve_obligation_callee: the credit and the obligation resolve the callee once)
//@ accept-means: the unannotated-loop walker resolves `f` to `make::<D>` through resolve_unique_call_fn_def and assumes `result == 7u32`, while assertion::call_type_obligation resolves `f` through the block-local find_local_assignment_rvalue, which scans only the CALL block's statements and therefore never sees the pre-loop assignment; `evil` panics in `<D as Drop>::drop` on every call with n > 0 and can never return.
//@ verdict: failed
//@ refused-with: evil unknown (refutation withheld: goal set carries a fail-closed
//@ teeth: measured — on the pre-fix merged head (439bbdba) this shape is `evil verified ✓`, 3 verified / 0 failed, exit 0 (review probe x10_false_accept_min.rs); on this head it is `evil FAILED ✗ (postcondition)`, exit 1.
//@ also-verified: make, need7
//@ teeth: D-141 RE-PIN (not a weakening). The tooth was `evil FAILED`, and that FAILED was a
//@ teeth: model of the path guard around the fail-closed `false` this case exists to owe:
//@ teeth: the violated goal was `g ==> false`, which every model of `g` refutes, so it showed
//@ teeth: only that the refused construct is reached.
//@ teeth: Its twin s62v2_preloop_fnptr_credit_no_owe_quiet_drop_control, whose contract is TRUE,
//@ teeth: printed `evil FAILED` with the counterexample `n = 1` on the build that read only a bare
//@ teeth: `false` as a marker, and the same `unknown` as this case on the build that reads a
//@ teeth: guarded one.
//@ teeth: The marker is still owed, so `evil` is still refused and cannot be credited; only
//@ teeth: the spelling changed, and `refused-with:` names this function's own refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct D;

impl Drop for D {
    fn drop(&mut self) {
        panic!("boom")
    }
}

// `make` drops its argument, so every call runs `<D as Drop>::drop`.
#[ensures(result == 7u32)]
pub fn make<T>(_t: T) -> u32 {
    7u32
}

#[requires(y == 7u32)]
#[ensures(true)]
pub fn need7(y: u32) {}

// `f` is assigned in the ENTRY block; the call `f(D)` lives in the loop body
// block. The whole-body backtracker pins `f` to `make::<D>`; the block-local
// one does not. Whichever resolver decides the credit must be the one that
// decides the drop-glue obligation, or this verifies while panicking.
#[ensures(true)]
pub fn evil(n: u32) {
    let f: fn(D) -> u32 = make::<D>;
    let mut i = 0u32;
    while i < n {
        let r = f(D);
        need7(r);
        i = i.wrapping_add(1u32);
    }
}
