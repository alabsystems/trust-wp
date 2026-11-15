//@ expect: reject
//@ mechanism: a BY-VALUE parameter written by a plain write that D-140's withdrawal does not see as a
//@ mechanism: re-binding, then a `proof_assert!` of the ENTRY value: a binding of a pattern parameter
//@ mechanism: (`(mut a, b): (u32, u32)`, `a = any()` under `#[requires(a@ == 0)]`) and a store through a
//@ mechanism: `Box` parameter (`*b = any()` under `#[requires((*b)@ == 0)]`). The proof_assert lane binds
//@ mechanism: `a` and `*b` to the value written (a write of 7 is proved `== 7`, and under the entry fact
//@ mechanism: `== 0` refused as a vacuous proof) and reads the precondition beside that binding, so the
//@ mechanism: entry fact constrains the call's result. The withdrawal reads a by-value parameter's
//@ mechanism: substitution under the parameter's own name: a pattern parameter's bindings are not
//@ mechanism: parameter names, and a store through the `Box` is not a re-binding of `b`. A plain
//@ mechanism: `x = any()` on a named scalar parameter is withdrawn (proof_assert_param_rebind_reads_entry_requires).
//@ mechanism: Found probing that withdrawal sideways; no drop is involved.
//@ accept-means: a `proof_assert!` is credited from a by-value parameter's entry precondition after the
//@ accept-means: body overwrote it with a value the precondition says nothing about, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: at each assertion the value is 9, what `any` returns; the precondition
//@ WHY THE CONTRACT IS FALSE: says only what it was at entry.
//@ fixed-by: OPEN: committed RED. Closing it means asking the withdrawal of every place a by-value
//@ fixed-by: parameter's entry fact names (a pattern binding, a `Box`'s content), not only the parameter's name.
//@ teeth: LIVE: each function ACCEPTED, exit 0, `proof_assert in creusot_test::<fn> verified`, on D-140's
//@ teeth: driver and on the campaign driver it branches from.
//@ teeth: Since D-177 the pattern spelling is closed: `a` in the requires is the parameter's
//@ teeth: projection, not the re-bound local, and `pattern_param` FAILED on its assertion. The `Box`
//@ teeth: spelling is still LIVE: `box_param` is credited `verified` on the false assertion, so the
//@ teeth: case stays RED as a false credit beside the refuted function.
//@ also-verified: any
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
#[ensures(true)]
pub fn any() -> u32 {
    9
}

#[requires(a@ == 0)]
pub fn pattern_param((mut a, b): (u32, u32)) {
    a = any();
    proof_assert!(a@ == 0);
    let _ = b;
}

#[requires((*b)@ == 0)]
pub fn box_param(mut b: Box<u32>) {
    *b = any();
    proof_assert!((*b)@ == 0);
}
