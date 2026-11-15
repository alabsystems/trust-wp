//@ expect: reject
//@ mechanism: D-142 takes a clause-free body's `assert!` arm out of the panic cap when the switch
//@ mechanism: lane's charge `!guard` is proved, and D-143 honors the proof when its premises are
//@ mechanism: entry facts. This proof has no premise at all: an `f64` reaches the solver as a real
//@ mechanism: number, where `x == x` holds, so the charge is proved and the arm is cut as dead. Rust
//@ mechanism: compares floats by IEEE-754, under which `f64::NAN == f64::NAN` is false, so the arm
//@ mechanism: runs. Before D-142 the cap counted the arm unchecked and the body reported `unknown
//@ mechanism: (partial: panic paths unchecked)`. The clause-free spelling of
//@ mechanism: f64_eq_reflexive_despite_nan.rs: D-142 widens the real-number reading of floats from
//@ mechanism: contracts to every clause-free body that asserts about a float.
//@ fixed-by: D-147 (narrows D-142): no switch edge is proved dead in a body that computes with a
//@ fixed-by: float, an integer complement or a shift, so the arm stays in the clause-free cap; D-215
//@ fixed-by: reads the comparison over IEEE-754, where the arm's charge is refuted.
//@ accept-means: a clause-free body that panics at `x = f64::NAN` is reported `verified`.
//@ WHY THE CONTRACT IS FALSE: `nan_eq(f64::NAN)` panics.
//@ verdict: failed
//@ teeth: ACCEPTED (`nan_eq verified`) under D-142 before D-147; `unknown (partial: panic paths
//@ teeth: unchecked)` with D-142's proved edges withheld (an A/B knob) and after D-147. Under D-215 the
//@ teeth: comparison is IEEE `==` and the charge is refuted at NaN (`nan_eq FAILED`, a validated model).
//@ teeth: The twin clause_free_f64_not_lt_self_control.rs is true under IEEE-754; D-147 caps it too.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn nan_eq(x: f64) {
    assert!(x == x);
}
