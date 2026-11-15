//@ expect: verify
//@ xfail: D-177 destructures the body to `__twp_arg1.x`, and the unfolded `(P { x: a, y: b }).x` is not
//@ xfail: reduced to `a`: a field read of a struct literal argument is not proved even with no
//@ xfail: pattern in sight (`#[ensures(result == p.x)] fn g(p: P)` called as `g(P { x: 7, y })` does
//@ xfail: not give `result == 7` either). The reject twin is refused for that reason too, not only for
//@ xfail: its false clause.
//@ mechanism: control for logic_open_impl_struct_pattern_param_captures_caller_name: the body returns `a`.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub x: Int,
    pub y: Int,
}
pub trait Tr {
    #[logic]
    fn v(self, pq: P) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn v(self, P { x, y: _ }: P) -> Int { x }
}
#[ensures(result@ == S.v(P { x: a@, y: b@ }))]
pub fn g(x: u32, a: u32, b: u32) -> u32 { a }
