//@ expect: reject
//@ verdict: failed
//@ refused-with: f unknown (refutation withheld: goal set carries a fail-closed
//@ also-verified: <S as Tr>::spin
//@ mechanism: the value twin of s40v2_trait_concrete_inert_requires: `f` calls the inert spin
//@ mechanism: only when `x > 0`, which meets the impl's `requires`, so `f`'s own contract is TRUE.
//@ mechanism: The trusted spin's `requires` is owed as a fail-closed `false` behind the branch's
//@ mechanism: path guard (`x > 0 ==> false`); a model of the guard refutes it, which shows only
//@ mechanism: that the call is reached (D-141, a guarded marker is a marker). The crate is still
//@ mechanism: rejected: the impl-only `requires` fails trait refinement.
//@ accept-means: the impl's `requires` is stronger than the trait declaration's, which refinement
//@ accept-means: must refuse whatever its callers do.
//@ WHY THE CONTRACT IS FALSE: `<S as Tr>::spin` requires `x > 0` where `Tr::spin` requires
//@ WHY THE CONTRACT IS FALSE: nothing, so the impl does not refine the trait.
//@ teeth: the pin is `f`'s own line: a TRUE function refuted only through the reachability of a
//@ teeth: construct trust-wp does not model must never print FAILED. Measured on the build that
//@ teeth: read only a bare `false` as a marker: `f FAILED` with the counterexample `x = 1`
//@ teeth: through the guarded marker, exactly as the RED twin's `x = 0`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr { fn spin(x: i32) -> !; }
pub struct S;
impl Tr for S { #[requires(x@ > 0)] fn spin(x: i32) -> ! { loop {} } }
#[ensures(true)]
pub fn f(x: i32) { if x > 0 { <S as Tr>::spin(x) } }
