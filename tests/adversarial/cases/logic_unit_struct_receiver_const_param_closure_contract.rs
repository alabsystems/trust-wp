//@ expect: reject
//@ mechanism: logic_unit_struct_receiver_const_param_shadows on a CLOSURE's contract: the
//@ mechanism: closure has no generics of its own, and the const parameter that shadows the unit
//@ mechanism: struct belongs to the enclosing function (the closure's generics parent).
//@ accept-means: the closure's `S` was typed as the module's unit struct although it is the
//@ accept-means: enclosing function's const parameter.
//@ WHY THE CONTRACT IS FALSE: `S.v()` is `<i64 as Tr>::v(S)`, which is 2, not 1.
//@ fixed-by: with logic_unit_struct_receiver_const_param_shadows (the generic-parameter guard in
//@ fixed-by: unit_struct_value_type).
//@ teeth: the closure reported verified (flagged by the per-function gate) at the head that
//@ teeth: introduced unit_struct_value_type.
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
pub fn f<const S: i64>() {
    let c = #[ensures(S.v() == 1)] || {};
    c();
}
