//@ expect: reject
//@ mechanism: `x + 1i32 > x` over `i32` in a closure contract of two attributes. The type-check
//@ mechanism: vehicle reads no closure that carries another attribute, so the clause has no type
//@ mechanism: check, and was read as mathematical integer arithmetic. In the pinned oracle it is
//@ mechanism: `Int32$BW$.add`, which wraps (D-135 item 3).
//@ accept-means: a closure clause's machine-integer operator was read as mathematical arithmetic.
//@ WHY THE CONTRACT IS FALSE: x = i32::MAX: x + 1 wraps to i32::MIN, below x.
//@ refused-with: written where no type check says what its operands are
//@ fixed-by: D-232
//@ teeth: `two_attributes::{closure#0} verified` at the campaign base; refused under D-232, which
//@ teeth: reads a clause no type check reads by syntax alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(stmt_expr_attributes, proc_macro_hygiene)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn two_attributes() {
    let c = #[requires(x >= 0i32)]
    #[ensures(x + 1i32 > x)]
    |x: i32| {};
    c(1i32);
}
