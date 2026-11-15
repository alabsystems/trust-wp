//@ expect: verify
//@ xfail: the tuple-of-`&mut` carrier has no working prophecy layer, so the TRUE claim about the
//@ xfail: written field is refuted as well — the same defect pointing in the false-reject
//@ xfail: direction. An XPASS here, with both adversarial twins still rejecting, is the signal
//@ xfail: that the layering was fixed rather than merely muted.
//@ mechanism: over-refusal control for the by-value tuple-of-`&mut` prophecy layer
//@ fixed-by: ?
//@ accept-means: n/a (control) — this contract is TRUE and must verify once the layer is real.
//@
//@ This is the TRUE twin of tuple_mut_field_prophecy_layering_literal: the same precondition, the
//@ same body, and the postcondition the body actually establishes. It and its adversarial twin
//@ differ only in a literal, so nothing but a prophecy carrying the correct final value can
//@ separate them; a fix that flips both has landed the inversion instead of the layer.
//@ teeth: n/a — over-refusal control. Refuted today with a counterexample on the same build where
//@ teeth: the adversarial twins are accepted, which is the finding, not an excuse.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*p.0 == 0)]
#[ensures(^p.0 == 9)]
pub fn m<'a>(p: (&'a mut i32, &'a mut i32)) {
    *p.0 = 9;
}
