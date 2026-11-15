//@ expect: verify
//@ mechanism: the boundary of the const-parameter refusal (unit_struct_value_type): identical to
//@ mechanism: logic_unit_struct_receiver_const_param_shadows except that the const parameter is
//@ mechanism: named `N`, so the clause's `S` IS the module's unit struct and `S.v()` is 1. The
//@ mechanism: pair differs only in whether a generic parameter shadows the name; the shadowed one
//@ mechanism: is refused and this one is resolved on the unit struct.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn v(self) -> Int { 1 }
}
impl Tr for i64 {
    #[logic(open)]
    fn v(self) -> Int { 2 }
}
#[ensures(S.v() == 1)]
pub fn f<const N: i64>() {}
