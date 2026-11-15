//@ expect: reject
//@ mechanism: `resolve(e)` of an operand that is neither a variable nor a dereference (a view `x@`, a
//@ mechanism: constructor `Some(*x)`) was read as `*e == ^e`, and the wrapper distributes `*` and `^`
//@ mechanism: into the operand: `(*x)@ == (^x)@`, `Some(*x) == Some(^x)`. Neither operand holds a
//@ mechanism: borrow, so its resolve is `true`; the reading is stronger, and false where negated.
//@ accept-means: a function is credited with `!true` about an integer or an `Option<i32>`.
//@ WHY THE CONTRACT IS FALSE: `x@` is an integer and `Some(*x)` an `Option<i32>`; neither holds a
//@ WHY THE CONTRACT IS FALSE: borrow, so its resolve is `true` in every run and `!resolve(..)` is false.
//@ fixed-by: D-127 (`resolve` of an operand that is not a variable is refused unless it is a
//@ fixed-by: dereference of a shared reference to a value)
//@ teeth: MEASURED (debug driver): before D-127 neg_view and neg_some verified; D-127 refuses both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x != 5i32)]
#[ensures(!resolve(x@))]
pub fn neg_view(x: &mut i32) {
    *x = 5;
}

#[requires(*x != 5i32)]
#[ensures(!resolve(Some(*x)))]
pub fn neg_some(x: &mut i32) {
    *x = 5;
}
