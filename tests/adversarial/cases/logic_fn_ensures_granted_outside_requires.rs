//@ expect: reject
//@ mechanism: a `#[logic]` function's POSTCONDITION reaches a caller through a SECOND emitter beside the SMT spec axiom — the structural precheck that discharges an obligation matching one instance of a visible logic fn's `ensures` — and that emitter consulted the fn's `ensures` alone, never its `#[requires]`; the SMT spec axiom and the defining axiom ARE guarded, so the grant and the obligation sat in different environments and the caller harvested `ensures` at arguments where the body it was proved from says nothing.
//@ accept-means: both clauses of one postcondition are granted at `-1`, giving `idl(-1) == -1` and `idl(-1) >= 0`; no integer satisfies both, so the asserted conjunction is UNSATISFIABLE and an accept is trust-wp reporting `verified` for `false` — every obligation sharing such a proof context is worthless.
//@ note: README rule 1 asks for a refuting execution and this case has none: `idl` is a
//@ note: logic function and the runtime body returns 1, which its own `ensures` allows.
//@ note: The asserted conjunction is UNSATISFIABLE instead, which is strictly worse than
//@ note: false-but-satisfiable -- it cannot be excused as a completeness gap.
//@ fixed-by: 96103354 (the structural precheck that matches an obligation against a
//@ fixed-by: visible logic fn's `ensures` now instantiates that fn's `requires` at the same
//@ fixed-by: arguments and fails closed unless it holds here; the guarded SMT spec axiom
//@ fixed-by: `forall args. requires => ensures` was already the only other emitter)
//@ teeth: measured ACCEPTED, exit 0 (`proof_assert ... verified`, `2 verified, 0 failed, 0 errors`), and ACCEPTED by the campaign-tip binary too, so the hole pre-exists this branch; attribution measured three ways — with both `ensures` clauses removed the identical assertion is `unknown` (the defining axiom is requires-guarded, fail-closed), with only `#[ensures(result == x)]` kept `idl(-1) == -1` alone is ACCEPTED, and the in-domain control verifies, so the accept is the out-of-domain grant and not a collapse of the assertion lane.
//@ also-verified: creusot_test::idl
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// `idl` is the identity on its declared domain `x >= 0`. Outside that domain the
// definition says nothing, so neither postcondition clause may be assumed there.
#[logic(open)]
#[requires(x >= 0)]
#[ensures(result == x)]
#[ensures(result >= 0)]
pub fn idl(x: Int) -> Int {
    x
}

#[ensures(result@ == 1)]
pub fn c() -> u32 {
    proof_assert!(idl(-1) == -1 && idl(-1) >= 0);
    1u32
}
