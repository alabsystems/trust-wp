//@ expect: reject
//@ mechanism: the rounding spelling of clause_free_f64_eq_assert_despite_nan.rs, with NaN excluded by
//@ mechanism: the guard: over the reals `x + 1.0 > x` holds, so the `assert!` arm's charge is proved
//@ mechanism: and D-142 cuts the arm. In `f64` the sum rounds: `1e16 + 1.0 == 1e16`, and
//@ mechanism: `f64::INFINITY + 1.0` is `f64::INFINITY`, so the arm runs.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift, so the arm stays in the clause-free cap; D-215
//@ fixed-by: reads the sum as IEEE `fp.add`, where the arm's charge can be refuted.
//@ accept-means: a clause-free body that panics at `x = 1e16` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `plus_one_gt(1e16)` panics.
//@ teeth: ACCEPTED (`plus_one_gt verified`) under D-142 before D-147; capped `unknown` with the
//@ teeth: proved dead edges withheld (an A/B knob) and after D-147. Under D-215 one binary reports it
//@ teeth: FAILED (the charge refuted at a rounding sum) or capped `unknown` (ay's floating-point path
//@ teeth: undecided) between runs, so the case pins no flavour of the rejection. The twin
//@ teeth: clause_free_f64_plus_one_assert_ge_control.rs differs in `>=`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn plus_one_gt(x: f64) {
    if x >= 0.0 {
        assert!(x + 1.0 > x);
    }
}
