//@ expect: reject
//@ mechanism: logic-fn identity — one local `impl View for A`; generic callee requires `u.view() == 0` with u: u32: the single local `view` definition answered for the u32 impl
//@ fixed-by: s35 logic-fn identity (singleton external-trait impl identities; x.view() without a local impl -> x@)
//@ accept-means: a local logic definition was applied to a receiver of a type it does not implement
//@ teeth: accepted with exit 0 on wp-campaign fd7534d
//@ also-verified: g
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl View for A { type ViewTy = Int; #[logic(open)] fn view(self) -> Int { pearlite!{0} } }
#[requires(u.view() == 0)]
pub fn g<T: View<ViewTy = Int>>(t: T, u: u32) {}
#[ensures(true)]
pub fn caller() { g(A, 7u32) }
