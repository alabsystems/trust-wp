//@ expect: verify
//@ mechanism: Final-collapse guard, CONSTANT-carrier arm x binder carve-out scoping —
//@ mechanism: over-refusal control for the quantifier-wrapped pair. The contract is TRUE
//@ mechanism: (read-only borrow, `x` keeps its value) and exists-wrapped: proving it requires
//@ mechanism: the existential witness machinery (witness probe / trivial-witness
//@ mechanism: instantiation) to still function, including its binder-erasing carve-out that
//@ mechanism: legitimately erases `i := 0` inside the wrapped body. Under #125 the erased
//@ mechanism: binder is normalised at the substitution site instead of minting
//@ mechanism: `Final(<literal>)`.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE. A REJECT here means the
//@ accept-means: prophecy-over-constant refusal (or the #125 evaluator hardening) is
//@ accept-means: over-broad: it is eating the legitimate binder-erasing lane and
//@ accept-means: quantified TRUE contracts over constant-valued locals no longer prove.
//@ teeth: n/a — over-refusal control. Passed BOTH arms (pristine 4d809ba and the fix
//@ teeth: 437233e/8d7bf70) of the tract19 leg4 gate probe run (2026-08-14), method (i).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// TRUE contract under an `exists` wrapper: the borrow is only read through,
/// so `x` keeps its value and the witness `i == 0` closes the existential.
#[ensures(exists<i: Int> i == 0 && result@ == 3)]
pub fn read_only_borrow_of_constant_exists_wrapped() -> i32 {
    let mut x = 3i32;
    let r = &mut x;
    let v = *r;
    return v;
}
