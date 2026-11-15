//@ expect: verify
//@ mechanism: open_logic_unfold.rs impl_method_param_names named a `_` parameter `arg{idx}`, duplicating a real parameter `arg{idx}`; the later binding won when the open impl body was unfolded.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ mechanism: The receiver is the unit struct value `S`, and `v` collides with the trait
//@ mechanism: declaration, so the call is resolved on the type that bare path denotes
//@ mechanism: (logic/identity.rs unit_struct_value_type); the control verifies only through that.
//@ teeth: control: verifies. It was refused ("the receiver's type is not known here") while a unit
//@ teeth: struct receiver had no Rust type in the resolver.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self, p: Int, q: Int, r: Int) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn v(self, _: Int, arg3: Int, _: Int) -> Int { arg3 }
}
#[ensures(result@ == S.v(a@, b@, c@))]
pub fn g(a: u32, b: u32, c: u32) -> u32 { b }
