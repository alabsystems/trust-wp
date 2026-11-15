//@ expect: reject
//@ mechanism: a logic method call `s.m()` names its callee by the method name and passes the receiver as the first parameter; the goal the logic lane owes binds `self` to the receiver (`logic_fn_verify::callee_preconditions`, `PureExpr::MethodCall`, and the call-rewritten `LogicFnCall` spelling alike).
//@ accept-means: a logic function that calls a method outside its precondition is credited `verified`.
//@ WHY IT IS FALSE: at `s.v == 0` the body calls `s.m()`, and `m` requires `self.v@ > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓`, the call never examined.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub v: i32,
}

impl S {
    #[logic]
    #[requires(self.v@ > 0)]
    pub fn m(self) -> Int {
        pearlite! { self.v@ }
    }
}

#[logic]
#[ensures(true)]
pub fn caller(s: S) -> Int {
    s.m()
}
