//@ expect: reject
//@ verdict: failed
//@ mechanism: a receiver-style call to a trait logic method whose receiver is a UNIT STRUCT VALUE
//@ mechanism: (`S.v(..)`) is resolved on the type the bare path `S` denotes in the owner's scope
//@ mechanism: (logic/identity.rs unit_struct_value_type). Two unit structs implement the same trait
//@ mechanism: with different open bodies, so only the impl of the receiver's own type states the
//@ mechanism: right value.
//@ accept-means: the call was resolved to the other unit struct's impl (or to any definition
//@ accept-means: not selected by the receiver's type).
//@ WHY THE CONTRACT IS FALSE: `S.v(a, b)` is `a` and `g` returns `b`; `g(0, 1)` returns 1.
//@ teeth: accepted when unit_struct_value_type typed the receiver as the OTHER unit struct of the
//@ teeth: module (a local knob, not committed); FAILED with the resolution as committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self, p: Int, q: Int) -> Int;
}
pub struct S;
pub struct T;
impl Tr for S {
    #[logic(open)]
    fn v(self, p: Int, _: Int) -> Int { p }
}
impl Tr for T {
    #[logic(open)]
    fn v(self, _: Int, q: Int) -> Int { q }
}
#[ensures(result@ == S.v(a@, b@))]
pub fn g(a: u32, b: u32) -> u32 { b }
