//@ expect: reject
//@ mechanism: the logic pass proved each logic function with every other function's `ensures` in scope as a spec axiom, whether or not that `ensures` had been proved. `g`'s claim is false and is refuted on its own; `f`'s claim follows only from `g`'s, and `f` was credited `verified ✓` on it, and `p` `verified*` on `f`'s. A callee whose obligation is already lost is now neutralized in the caller's proof environment, as every downstream consumer reads it.
//@ accept-means: a logic function credited on a callee's unproved `ensures`, and a program function credited on that.
//@ WHY IT IS FALSE: `h(x)` is `x`, so `g(x) = f(x) = x`, and `result > x` holds for none of them.
//@ verdict: unknown
//@ teeth: measured with the environment neutralization knocked out: `creusot_test::g postcondition FAILED (logic postcondition)`, then `creusot_test::f verified ✓` and `p verified* (depends on 1 unverified axiom(s))`, both credits TEETH LOST; the stale-credit withdrawal does not catch it, because `g` was already lost when `f`'s environment was built. The twin whose `g` is `x + 1` verifies at exit 0 with the fix (logic_fn_callee_proved_ensures_control.rs).
//@ fixed-by: D-159 (a callee lost before the caller's proof environment is built is neutralized in it)
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
pub fn g(x: Int) -> Int {
    h(x)
}

#[logic]
#[ensures(result > x)]
pub fn f(x: Int) -> Int {
    g(x)
}

#[ensures(f(0int) > 0)]
pub fn p() {}
