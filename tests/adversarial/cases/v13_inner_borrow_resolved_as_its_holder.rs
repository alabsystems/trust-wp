//@ expect: reject
//@ mechanism: `encode_resolve` stripped every `*` of its operand and read `resolve(*x)` as the resolve
//@ mechanism: of `x` itself (#508), and read `resolve(x.f)` as `*e == ^e` distributed into the
//@ mechanism: projection, `(*x).f == (^x).f`. Where the operand is itself a borrow held through `x`
//@ mechanism: (`*x: &mut i32`, `**x`, `**x` of a `&mut Box<&mut i32>`, `x.0`, `x.m`, or a referent
//@ mechanism: that holds one), its resolve is `*e == ^e` of THAT borrow, whose final value the caller
//@ mechanism: decides; the outer borrow's resolve says only that the holder was left unchanged, true
//@ mechanism: of an empty body. The spelled `^x.m == *x.m` was placed as `(^x).m == (*x).m` the
//@ mechanism: same way.
//@ accept-means: a function is credited with the claim that a borrow its caller keeps (and may
//@ accept-means: write through after the call) is resolved at the return.
//@ WHY THE CONTRACT IS FALSE: each operand is (or holds) the caller's inner borrow: the caller can
//@ WHY THE CONTRACT IS FALSE: write 5 through it after the call while its value at the call is 3,
//@ WHY THE CONTRACT IS FALSE: so `*e == ^e` of it is no fact of the function.
//@ fixed-by: D-127 (`resolve` reads its operand at the operand's own type and refuses a value held
//@ fixed-by: through a variable; a final value read of a value held through a `&mut` parameter is
//@ fixed-by: refused where the contract is placed)
//@ teeth: MEASURED (debug driver): before D-127 every function here verified; D-127 refuses each.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

#[ensures(resolve(*x))]
pub fn nested_untouched(x: &mut &mut i32) {}

#[ensures(resolve(**x))]
pub fn triple(x: &mut &mut &mut i32) {}

#[ensures(resolve(**x))]
pub fn boxed_inner(x: &mut Box<&mut i32>) {}

#[ensures(resolve(*x))]
pub fn generic_deref<T>(x: &mut T) {}

#[ensures(resolve(*x))]
pub fn struct_deref(x: &mut M<'_>) {}

#[ensures(resolve(x.0))]
pub fn inner_field(x: &mut (&mut i32, i32)) {}

#[ensures(resolve(x.m))]
pub fn struct_inner(x: &mut M<'_>) {}

#[ensures(^x.m == *x.m)]
pub fn struct_inner_spelled(x: &mut M<'_>) {}
