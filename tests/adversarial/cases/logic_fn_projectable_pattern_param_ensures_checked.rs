//@ expect: reject
//@ verdict: error
//@ refused-with: creusot_test::k postcondition FAILED (logic postcondition)
//@ also-verified: g
//@ mechanism: the by-value twin of logic_fn_unprojectable_pattern_param_clauses_unexamined: the
//@ mechanism: pattern binding `p` IS a projection of the parameter (`__twp_arg0.0`), so D-177 states the
//@ mechanism: body and the `ensures` over it and the logic function's own `ensures` is checked.
//@ accept-means: `k`'s false `ensures` was not checked against its body.
//@ WHY THE CONTRACT IS FALSE: `k((1, 0))` is 1, not above 1000. `g` is true and is credited on
//@ WHY THE CONTRACT IS FALSE: purpose.
//@ fixed-by: n/a — the boundary of D-177's refusal: a projectable binding is destructured, not refused.
//@ teeth: `creusot_test::k postcondition FAILED (logic postcondition)` at the head that introduced
//@ teeth: D-177, with or without the run refusal of its unprojectable twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
#[ensures(result > 1000)]
pub fn k((p, _q): (Int, Int)) -> Int { p }

#[ensures(result == 1u32)]
pub fn g() -> u32 { 1 }
