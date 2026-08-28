//@ expect: reject
//@ mechanism: Final-collapse guard, CONSTANT-carrier arm x binder carve-out scoping. Same defect
//@ mechanism: as f_prophecy_over_constant_carrier (the driver advances a borrow-chain base local
//@ mechanism: with a constant value as `Final(<literal>)`, and folding `^<literal>` asserts
//@ mechanism: `^p == *p`), with the FALSE contract wrapped in an `exists`. The wrapper probes the
//@ mechanism: fix's one carve-out: binder-erasing substitution (the existential witness probe
//@ mechanism: x := 0/1/-1) legitimately produces `Final(<literal>)` from `^x` and is allowed to
//@ mechanism: fold, marked by QuantifierState::binder_substitution_depth. That marker is a SCOPE
//@ mechanism: marker, not quantifier depth — a prophecy-over-constant that was NOT minted by the
//@ mechanism: binder substitution must stay refused even inside a quantified postcondition, and
//@ mechanism: the no-solve trivially-true accepting path (verify/postcondition.rs, #125) must
//@ mechanism: refuse `Final(<literal>)` under the binder too.
//@ fixed-by: tract19 437233e (landed as 8d7bf70, AYEncoder::refuse_prophecy_over_constant); the
//@ fixed-by: solver-bypassing accepting evaluators additionally hardened by #125
//@ accept-means: quantifier wrapping launders the constant-carrier collapse: any false contract
//@ accept-means: about the post-state of a mutated local borrow becomes provable by writing
//@ accept-means: `exists<i: Int> i == 0 && <false contract>` — the binder carve-out has leaked
//@ accept-means: from the erased binder to ambient scope.
//@ teeth: PROVEN, method (i) — historical-commit accept, not a reconstruction: this probe was
//@ teeth: ACCEPTED (verified, exit 0) on pristine 4d809ba x ay ba6c479fc by the tract19 leg4
//@ teeth: gate (2026-08-14, execution-log entry "THIRD LIVE FALSE ACCEPT"), and rejected at the
//@ teeth: fix arm 437233e/8d7bf70 with the TRUE exists-wrapped control passing both arms.
//@ teeth: Recorded per method (i) rather than re-running the historical build.
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

/// FALSE contract under an `exists` wrapper: after `touch(r)` and `r`'s
/// expiry, `x` is 99, so no witness makes `result@ == 3` true.
#[ensures(exists<i: Int> i == 0 && result@ == 3)]
pub fn prophecy_over_literal_exists_wrapped() -> i32 {
    let mut x = 3i32;
    let r = &mut x;
    touch(r);
    return x;
}
