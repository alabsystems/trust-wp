//@ expect: reject
//@ mechanism: Final-collapse guard, CONSTANT-carrier arm x binder carve-out scoping — the
//@ mechanism: universal twin of f_prophecy_over_constant_exists_wrap. The FALSE contract is
//@ mechanism: wrapped in a `forall`. 8d7bf70's carve-out is explicitly a scope marker for
//@ mechanism: binder-ERASING substitution, NOT quantifier depth ("a postcondition wrapped in
//@ mechanism: `forall<i> ...` stays refused"): a universal binder is skolemized/kept, never
//@ mechanism: erased to a ground witness, so nothing licenses folding `Final(<literal>)` in its
//@ mechanism: body. The trivially-true no-solve path (verify/postcondition.rs recurses through
//@ mechanism: Forall/Implies shapes, #125) must refuse it as well.
//@ fixed-by: tract19 437233e (landed as 8d7bf70, AYEncoder::refuse_prophecy_over_constant); the
//@ fixed-by: solver-bypassing accepting evaluators additionally hardened by #125
//@ accept-means: quantifier wrapping launders the constant-carrier collapse on the universal
//@ accept-means: side: `forall<i: Int> i == i ==> <false contract>` becomes provable, i.e. the
//@ accept-means: refusal is being keyed on quantifier depth instead of binder-erasing scope and
//@ accept-means: any quantified contract over a mutated local borrow is discharged pre-state.
//@ teeth: PROVEN, method (i) — historical-commit accept, not a reconstruction: this probe was
//@ teeth: ACCEPTED (verified, exit 0) on pristine 4d809ba x ay ba6c479fc by the tract19 leg4
//@ teeth: gate (2026-08-14, execution-log entry "THIRD LIVE FALSE ACCEPT"), and rejected at the
//@ teeth: fix arm 437233e/8d7bf70. Recorded per method (i) rather than re-running the
//@ teeth: historical build.
//@ also-verified: touch
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// TRUE contract, deliberately not an equality on the prophecy.
#[ensures((^r)@ >= 0)]
fn touch(r: &mut i32) {
    *r = 99;
}

/// FALSE contract under a `forall` wrapper: after `touch(r)` and `r`'s
/// expiry, `x` is 99, so the body is false at every instantiation.
#[ensures(forall<i: Int> i == i ==> result@ == 3)]
pub fn prophecy_over_literal_forall_wrapped() -> i32 {
    let mut x = 3i32;
    let r = &mut x;
    touch(r);
    return x;
}
