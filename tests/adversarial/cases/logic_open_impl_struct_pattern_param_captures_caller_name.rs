//@ expect: reject
//@ mechanism: a logic function whose parameter is a destructuring PATTERN (`(p, _q): (Int, Int)`)
//@ mechanism: is registered with a positional fallback name for that parameter (name_unnamed_params:
//@ mechanism: a non-`Binding` pattern is unnamed), while its body text still says `p`. `p` is then
//@ mechanism: bound by nothing in the definition, and unfolding the body at a use site substitutes
//@ mechanism: the parameters only, so the free `p` is read in the CALLER's scope: here it is captured
//@ mechanism: by the caller's own parameter `p`. Creusot destructures the argument (`let (p, _) = x`).
//@ mechanism: Here the pattern is a STRUCT pattern (`P { x, y: _ }: P`) and the captured name is `x`.
//@ accept-means: the unfolded body's pattern binding `x` was read as the caller's parameter `x`.
//@ WHY THE CONTRACT IS FALSE: `S.v(P { x: a, y: b })` is `a`; `g(5, 1, 2)` returns 5, not 1.
//@ fixed-by: D-177 — open_logic_unfold destructures the impl body before unfolding it (`x` is
//@ fixed-by: `__twp_arg1.x`), and does not unfold a body that mentions a binding with no projection. Its
//@ fixed-by: control is an xfail: a field read of the unfolded struct literal is not proved
//@ fixed-by: (logic_open_impl_struct_pattern_param_captures_caller_name_control).
//@ teeth: ACCEPTED (exit 0) at the reviewed head; refused before D-172 typed the unit-struct receiver.
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
pub fn g(x: u32, a: u32, b: u32) -> u32 { x }
