//@ expect: reject
//@ verdict: failed
//@ mechanism: open_logic_unfold.rs impl_method_param_names named a `_` parameter `arg{idx}`, duplicating a real parameter `arg{idx}`; the later binding won when the open impl body was unfolded.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: S.v(a, b, c) was unfolded to c.
//@ teeth: `_` after the receiver and at the end; real `arg3` in the middle.
//@ teeth: The rejection is pinned to a counterexample: while the unit struct receiver `S` had no
//@ teeth: Rust type in the logic-identity resolver, this case was rejected by that refusal instead,
//@ teeth: which says nothing about the parameter naming it targets.
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
pub fn g(a: u32, b: u32, c: u32) -> u32 { c }
