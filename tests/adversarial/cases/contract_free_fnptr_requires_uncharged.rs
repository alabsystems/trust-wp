//@ expect: reject
//@ verdict: failed
//@ fn-failed: hop
//@ mechanism: the contract-free discovery predicate read the callee identity ONLY off
//@ mechanism: `Operand::Constant` with an `FnDef` type (`body_calls_requires_bearing_callee`).
//@ mechanism: Reified into a `fn` pointer the operand is a `Copy`/`Move` of a local, so the
//@ mechanism: predicate saw no contracted callee and this contract-free host was a verification
//@ mechanism: target of NOTHING — while the CALL lane does charge the precondition through the
//@ mechanism: same pointer (the contracted-host twin of this body is refuted). Grant and
//@ mechanism: obligation were the same fact read by two pieces of code that disagreed: reading a
//@ mechanism: callee the pass cannot NAME as "no precondition owed here" is an
//@ mechanism: under-approximation, and an under-approximation in a discovery predicate costs a
//@ mechanism: credit rather than a walk.
//@ accept-means: a `#[requires]` is laundered by reifying the callee as a function pointer inside
//@ accept-means: a function with no contract — every contracted function in the crate is callable
//@ accept-means: outside its precondition with a clean, exit-0 verification run
//@ fixed-by: D-73
//@ teeth: ACCEPTED (exit 0, `2 verified, 0 failed, 0 errors`, `hop` named in no verdict line at
//@ teeth: all) both before and after the contract-free target rule of D-71; the contract is
//@ teeth: refutable by the body's single execution — compiled and run as a plain program it
//@ teeth: panics with `attempt to divide by zero`. The identical call in a host that carries a
//@ teeth: contract IS refuted, so the obligation exists and only the discovery predicate was
//@ teeth: blind to the site. It is not a blanket refusal of indirect calls that closes this:
//@ teeth: contract_free_fnptr_requires_control passes 1 through the SAME reified pointer and
//@ teeth: still verifies, and the clause-free twin of THIS body with a 1 argument is not refuted
//@ teeth: either — it is demoted by the cap, `unknown`, not `failed`.
//@ also-verified: need, anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(y@ != 0u32@)]
#[ensures(result@ == 10u32@ / y@)]
pub fn need(y: u32) -> u32 {
    10u32 / y
}

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// `need`'s precondition is violated here, through a function pointer.
pub fn hop() {
    let f: fn(u32) -> u32 = need;
    let _ = f(0u32);
}
