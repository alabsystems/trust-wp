//@ expect: reject
//@ verdict: failed
//@ mechanism: open_logic_unfold.rs impl_method_param_names named a `_` parameter `arg{idx}`, duplicating a real parameter `arg{idx}`; the later binding won when the open impl body was unfolded.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: S.v(a, b) was unfolded to b.
//@ teeth: exit-0 false accept on wp-campaign 3eede3c2 (review rev28b/l3); FAILED after the fix.
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
    fn v(self, p: Int, q: Int) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn v(self, arg2: Int, _: Int) -> Int { arg2 }
}
// WRONG: S.v(a, b) == a, and the body returns b.
#[ensures(result@ == S.v(a@, b@))]
pub fn g(a: u32, b: u32) -> u32 { b }
