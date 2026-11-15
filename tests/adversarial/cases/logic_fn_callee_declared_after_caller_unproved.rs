//@ expect: reject
//@ mechanism: the caller-before-callee order of logic_fn_callee_unproved_ensures_credits_caller.rs. `f` is proved first, while `g`'s false `ensures` is still in its environment; `g` is refuted afterwards. The credit rests on an axiom lost after the proof, so it is withdrawn (`verdict withdrawn - it reaches`), and `f`'s own axiom with it.
//@ accept-means: a logic function's credit outlived the callee `ensures` it was proved on.
//@ WHY IT IS FALSE: `h(x)` is `x`, so `g(x) = f(x) = x`, and `result > x` holds for none of them.
//@ verdict: unknown
//@ teeth: measured with the stale-credit withdrawal knocked out: `creusot_test::f verified ✓` printed before `creusot_test::g postcondition FAILED (logic postcondition)`, and `p verified*`, both credits TEETH LOST; the environment neutralization cannot catch it, because `g` is lost only after `f`'s proof. The twin whose `g` is `x + 1` keeps `f`'s credit and verifies at exit 0 with the fix (logic_fn_callee_declared_after_caller_proved_control.rs).
//@ fixed-by: D-159 (a credit whose goal reaches an axiom lost after its proof is withdrawn)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(opaque)]
pub fn h(x: Int) -> Int {
    x
}

#[logic]
#[ensures(result > x)]
pub fn f(x: Int) -> Int {
    g(x)
}

#[logic]
#[ensures(result > x)]
pub fn g(x: Int) -> Int {
    h(x)
}

#[ensures(f(0int) > 0)]
pub fn p() {}
