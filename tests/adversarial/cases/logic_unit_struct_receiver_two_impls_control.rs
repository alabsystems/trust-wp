//@ expect: verify
//@ mechanism: the TRUE twin of logic_unit_struct_receiver_two_impls: each unit struct's call
//@ mechanism: states its own impl's body, so `S.v` is the first argument and `T.v` the second.
//@ mechanism: Before the receiver was typed from the unit struct path, both calls were refused
//@ mechanism: ("the receiver's type is not known here").
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
pub fn g(a: u32, b: u32) -> u32 { a }
#[ensures(result@ == T.v(a@, b@))]
pub fn h(a: u32, b: u32) -> u32 { b }
