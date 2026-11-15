//@ expect: verify
//@ mechanism: the TRUE twin of logic_unit_struct_receiver_callee_text: the caller is granted
//@ mechanism: `result@ == T.v(1, 2)`, which is 2.
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
#[ensures(result@ == T.v(a@, b@))]
pub fn h(a: u32, b: u32) -> u32 { b }
#[ensures(result == 2u32)]
pub fn k() -> u32 { h(1, 2) }
