//@ expect: reject
//@ mechanism: a logic function whose parameter is a destructuring PATTERN (`(p, _q): (Int, Int)`)
//@ mechanism: is registered with a positional fallback name for that parameter (name_unnamed_params:
//@ mechanism: a non-`Binding` pattern is unnamed), while its body text still says `p`. `p` is then
//@ mechanism: bound by nothing in the definition, and unfolding the body at a use site substitutes
//@ mechanism: the parameters only, so the free `p` is read in the CALLER's scope: here it is captured
//@ mechanism: by the caller's own parameter `p`. Creusot destructures the argument (`let (p, _) = x`).
//@ mechanism: Here the receiver is a parameter `s: S`, typed without D-172.
//@ accept-means: the unfolded body's pattern binding `p` was read as the caller's parameter `p`.
//@ WHY THE CONTRACT IS FALSE: `s.v((a, b))` is `a`; `g(S, 5, 1, 2)` returns 5, not 1.
//@ fixed-by: D-177 — open_logic_unfold destructures the impl body before unfolding it (`p` is
//@ fixed-by: `__twp_arg1.0`), and does not unfold a body that mentions a binding with no projection.
//@ teeth: ACCEPTED (exit 0) at the reviewed head and at its base alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self, pq: (Int, Int)) -> Int;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn v(self, (p, _q): (Int, Int)) -> Int { p }
}
#[ensures(result@ == s.v((a@, b@)))]
pub fn g(s: S, p: u32, a: u32, b: u32) -> u32 { p }
