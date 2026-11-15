//@ expect: verify
//@ xfail: the clause's `S` is a const parameter, and unit_struct_value_type gives a name that a
//@ xfail: generic parameter shadows no type, so the receiver-style call is refused (it was refuted
//@ xfail: with the unit struct's impl before the guard; see logic_unit_struct_receiver_const_param_shadows).
//@ mechanism: the TRUE twin of logic_unit_struct_receiver_const_param_shadows: identical except
//@ mechanism: that the clause states the value of the i64 impl the const parameter selects.
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
#[ensures(S.v() == 2)]
pub fn f<const S: i64>() {}
