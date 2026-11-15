//@ expect: reject
//@ mechanism: a concrete, resolved, inert trait impl -> ! callee whose requires is ONLY on the impl, reached as a trusted spin
//@ accept-means: S::spin requires x > 0 and f(0) calls it with 0. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: A/B 2026-09-13 on 248e7b79 with the primary.rs trusted-spin requires fail-closed push removed: TEETH LOST (`f FAILED` not reported); fn-failed is required because the impl-only requires also fails trait refinement
//@ refused-with: f unknown (refutation withheld: goal set carries a fail-closed
//@ also-verified: <S as Tr>::spin
//@ teeth: D-141 RE-PIN (not a weakening). The tooth was `f FAILED`, and that FAILED was a
//@ teeth: model of the path guard around the fail-closed `false` this case exists to owe:
//@ teeth: the violated goal was `g ==> false`, which every model of `g` refutes, so it showed
//@ teeth: only that the refused construct is reached.
//@ teeth: Its twin s40v2_trait_concrete_inert_requires_met, whose contract is TRUE,
//@ teeth: printed `f FAILED` with the counterexample `x = 1` on the build that read only a bare
//@ teeth: `false` as a marker, and the same `unknown` as this case on the build that reads a
//@ teeth: guarded one.
//@ teeth: The marker is still owed, so `f` is still refused and cannot be credited; only
//@ teeth: the spelling changed, and `refused-with:` names this function's own refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr { fn spin(x: i32) -> !; }
pub struct S;
impl Tr for S { #[requires(x@ > 0)] fn spin(x: i32) -> ! { loop {} } }
#[ensures(true)]
pub fn f(x: i32) { if x <= 0 { <S as Tr>::spin(x) } }
