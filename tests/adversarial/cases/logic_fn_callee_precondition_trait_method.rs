//@ expect: reject
//@ mechanism: a call through a generic trait method `T::m(y)` owes the trait declaration's `requires`: every contracted definition the call's spelling may denote is a candidate (`logic_fn_verify::callee_preconditions`, `may_denote`).
//@ accept-means: a trait logic method's precondition is never owed at a generic call.
//@ WHY IT IS FALSE: at `y == 0` the body calls `T::m(0)`, and `m` requires `x > 0` for every implementation.
//@ teeth: MEASURED on the commit before D-119: not accepted, but only because the ensures lane refused the ambiguous `T::m` (`unknown`, exit 2); the call was never examined.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::caller
//@ note: no control: the ensures lane refuses the generic call `T::m` as ambiguous, so a caller
//@ note: inside the precondition does not verify either.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[requires(x > 0)]
    fn m(x: Int) -> Int;
}

#[logic]
#[ensures(true)]
pub fn caller<T: Tr>(y: Int) -> Int {
    T::m(y)
}
