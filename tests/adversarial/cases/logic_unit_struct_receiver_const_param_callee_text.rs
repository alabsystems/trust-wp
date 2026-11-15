//@ expect: reject
//@ also-verified: h
//@ mechanism: logic_unit_struct_receiver_const_param_shadows in the CALLEE-TEXT lane
//@ mechanism: (identity_typed.rs resolve_family_calls_in_text, `typed_on_param` falling back to
//@ mechanism: unit_struct_value_type): `h`'s TRUE contract travels to `k` as text whose `S`
//@ mechanism: is typed as the unit struct, so `k` is granted `result == 1` for a call that returns 2.
//@ accept-means: `k` was verified from a callee postcondition read with the unit struct's impl
//@ accept-means: in place of the one `h`'s const parameter selects.
//@ WHY THE CONTRACT IS FALSE: `h::<5>()` returns 2, and `k` claims 1. (`h`'s own contract is
//@ WHY THE CONTRACT IS FALSE: TRUE: its `S.v()` is the i64 impl's 2.)
//@ fixed-by: with logic_unit_struct_receiver_const_param_shadows (the generic-parameter guard in
//@ fixed-by: unit_struct_value_type).
//@ teeth: `k verified` with `h FAILED` at the head that introduced unit_struct_value_type (the
//@ teeth: per-function gate flags `k`); before it the text lane refused the receiver.
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
#[ensures(result@ == S.v())]
pub fn h<const S: i64>() -> i64 { 2 }

#[ensures(result == 1i64)]
pub fn k() -> i64 { h::<5>() }
