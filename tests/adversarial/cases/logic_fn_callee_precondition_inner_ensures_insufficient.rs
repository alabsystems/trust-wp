//@ expect: reject
//@ mechanism: the reject twin of logic_fn_callee_precondition_from_inner_ensures_control: the outer call's argument is the inner call's result, and the inner call's `ensures` (`result == x`) makes it `0` at `y == 1`, outside the outer call's precondition. The callee-precondition goal may assume a callee's `ensures` only where that callee's own precondition holds, and here it does, so what fails is the outer precondition itself.
//@ accept-means: a logic function whose nested call is outside its callee's precondition at an argument its own precondition admits is credited `verified`.
//@ WHY IT IS FALSE: at `y == 1`, which `caller`'s `y > 0` admits, `needs_pos(1) - 1 == 0` and `caller` calls `needs_pos(0)`; `needs_pos` requires `x > 0`, so Creusot's `vc_caller` is invalid.
//@ teeth: the rejection is the callee-precondition line alone (`caller unknown (logic callee precondition not proved)`) while the ensures `true` is proved; the ensures lane is the one that ACCEPTED logic_fn_callee_precondition_never_examined before D-119. Not measured on a build without D-119. The control, logic_fn_callee_precondition_inner_ensures_insufficient_control.rs, differs in `y > 1` alone.
//@ fixed-by: D-119
//@ also-verified: creusot_test::needs_pos
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
#[ensures(result == x)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[requires(y > 0)]
#[ensures(true)]
pub fn caller(y: Int) -> Int {
    needs_pos(needs_pos(y) - 1)
}
