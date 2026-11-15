//@ expect: verify
//@ mechanism: a promoted constant CTFE cannot hand back as a scalar or a newtype (`&Some(42)`, `&(3, 4)`) is read off the promoted's own MIR body by the primary extractor (`translate_promoted_body`), and kept only when CTFE evaluates the promoted, the extraction marked nothing it could not model, and the value is closed (no placeholder variable, whose spelling is derived from the promoted body's local indices and would name one of the enclosing function's values).
//@ mechanism: control: the payload read through `&Some(43)` is 43. Twin of promoted_const_enum_field_read.rs.
//@ accept-means: n/a (control)
//@ teeth: without the translation the promoted is an unconstrained placeholder and this TRUE contract is refuted, `promoted_field FAILED` with the counterexample `result = 0`.
//@ fixed-by: D-167 — a promoted's value is read off its own MIR body
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 43)]
pub fn promoted_field() -> i32 {
    match &Some(43) {
        Some(v) => *v,
        None => 0,
    }
}
