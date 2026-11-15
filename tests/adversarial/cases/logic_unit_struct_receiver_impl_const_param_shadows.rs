//@ expect: reject
//@ mechanism: logic_unit_struct_receiver_const_param_shadows with the const parameter on the
//@ mechanism: enclosing IMPL: the owner's own generics are empty, and the parameter that
//@ mechanism: shadows the unit struct is one generics-parent up.
//@ accept-means: the receiver `S` was typed as the module's unit struct although the clause's
//@ accept-means: `S` is the impl's const parameter.
//@ WHY THE CONTRACT IS FALSE: `S.v()` is `<i64 as Tr>::v(S)`, which is 2, not 1.
//@ fixed-by: with logic_unit_struct_receiver_const_param_shadows (the generic-parameter guard in
//@ fixed-by: unit_struct_value_type).
//@ teeth: ACCEPTED (exit 0) at the head that introduced unit_struct_value_type; before it the
//@ teeth: receiver had no Rust type and the call was refused.
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
pub struct W<const N: i64>;
impl<const S: i64> W<{ S }> {
    #[ensures(S.v() == 1)]
    pub fn f(&self) {}
}
