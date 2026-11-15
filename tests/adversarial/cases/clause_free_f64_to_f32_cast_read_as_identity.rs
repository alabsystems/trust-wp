//@ expect: reject
//@ mechanism: D-142 cuts a clause-free body's `assert!` arm when the walk's charge is proved from
//@ mechanism: entry facts. Floats reach the solver as real numbers and a narrowing `f64 as f32` is
//@ mechanism: read as the identity, so `(x as f32) as f64 == x` is proved; in IEEE-754 the cast
//@ mechanism: rounds `0.1f64` to the nearest `f32`, which is not `0.1f64`. Before D-142 the cap
//@ mechanism: counted the arm unchecked. f64_to_f32_cast_read_as_identity.rs is the contracted
//@ mechanism: spelling (the core defect); D-142 widens it to every clause-free body.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift, so the arm stays in the clause-free cap; D-215
//@ fixed-by: reads the cast as IEEE rounding, where the arm's charge is refuted.
//@ accept-means: a clause-free body that panics at `x = 0.1` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `roundtrip(0.1)` panics: `0.1f64 as f32 as f64` is
//@ WHY THE CONTRACT IS FALSE: `0.10000000149011612`.
//@ verdict: failed
//@ teeth: ACCEPTED (`roundtrip verified`) under D-142 before D-147; `unknown (partial: panic paths
//@ teeth: unchecked)` with the proved dead edges withheld (an A/B knob) and after D-147. Under D-215 the
//@ teeth: cast rounds and the charge is refuted (`roundtrip FAILED`, a validated model). The twin
//@ teeth: clause_free_f64_to_f32_cast_exact_control.rs asserts at a value `f32` holds exactly.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn roundtrip(x: f64) {
    if x == 0.1 {
        assert!((x as f32) as f64 == x);
    }
}
