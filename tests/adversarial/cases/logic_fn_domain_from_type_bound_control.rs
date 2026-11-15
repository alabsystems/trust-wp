//@ expect: verify
//@ xfail: over-refusal introduced by the domain guard, and a solver gap it had been masking.
//@ xfail: `n: u32` puts `n@ >= 0` in `idl`'s declared domain by TYPE, not by any clause, so
//@ xfail: `logic_fn_spec_domain_holds` cannot establish the antecedent and declines; the
//@ xfail: obligation then falls to the solver, which holds the guarded
//@ xfail: `forall x. x >= 0 ==> idl(x) == x` but does not answer from the parameter's range
//@ xfail: fact. Before the guard, the unguarded precheck discharged this structurally — it
//@ xfail: was both unsound and hiding the gap. XPASS means the domain check learned
//@ xfail: type-derived bounds, or the guarded axiom started firing on the range fact.
//@ mechanism: an in-domain use whose domain comes from the parameter's type rather than a
//@ mechanism: `requires` clause — the completeness price of D-50, kept visible.
//@ fixed-by: ?
//@ accept-means: n/a (control) — this contract is TRUE: `u32@` is never negative, so `idl`
//@ accept-means: is applied strictly inside `requires(x >= 0)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic(open)]
#[requires(x >= 0)]
#[ensures(result == x)]
#[ensures(result >= 0)]
pub fn idl(x: Int) -> Int {
    x
}

#[ensures(result@ == 1)]
pub fn c(n: u32) -> u32 {
    proof_assert!(idl(n@) == n@ && idl(n@) >= 0);
    1u32
}
