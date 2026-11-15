//@ expect: reject
//@ mechanism: logic_unit_struct_receiver_const_param_shadows in a proof_assert: the same
//@ mechanism: resolver types the receiver of an assertion in the body of `f<const S: i64>`.
//@ accept-means: the assertion's receiver `S` was typed as the module's unit struct although it
//@ accept-means: is the const parameter.
//@ WHY THE CONTRACT IS FALSE: `S.v()` is `<i64 as Tr>::v(S)`, which is 2, not 1.
//@ fixed-by: with logic_unit_struct_receiver_const_param_shadows (the generic-parameter guard in
//@ fixed-by: unit_struct_value_type).
//@ teeth: ACCEPTED (exit 0, the proof_assert verified) at the head that introduced
//@ teeth: unit_struct_value_type; before it the receiver had no Rust type and was refused.
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
    proof_assert!(S.v() == 1);
}
