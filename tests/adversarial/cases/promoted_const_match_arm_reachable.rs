//@ expect: reject
//@ mechanism: a promoted constant CTFE cannot hand back as a scalar or a newtype (`&Some(42)`, `&(3, 4)`) is read off the promoted's own MIR body by the primary extractor (`translate_promoted_body`), and kept only when CTFE evaluates the promoted, the extraction marked nothing it could not model, and the value is closed (no placeholder variable, whose spelling is derived from the promoted body's local indices and would name one of the enclosing function's values).
//@ mechanism: here `match (&Some(42), &None)` takes its `(Some(_), None)` arm, which panics.
//@ accept-means: a contract-free body whose panic arm is taken on every execution is credited as panic-free.
//@ WHY THE CONTRACT IS FALSE: `promoted_half()` panics (a contract-free fn is checked under `requires true`).
//@ teeth: control for the translation, not a regression test of a hole: never accepted. Without the translation the run is `unknown` (refutation withheld: solver evidence was unknown), which this case's `verdict: failed` does not accept; with it the panic arm is refuted, `promoted_half FAILED`. promoted_const_match_arm_unreachable_control.rs is its twin and is xfail.
//@ verdict: failed
//@ fn-failed: promoted_half
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn promoted_half() {
    match (&Some(42), &None::<i32>) {
        (Some(_), None) => panic!(),
        _ => (),
    }
}
