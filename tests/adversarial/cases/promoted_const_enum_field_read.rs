//@ expect: reject
//@ mechanism: a promoted constant CTFE cannot hand back as a scalar or a newtype (`&Some(42)`, `&(3, 4)`) is read off the promoted's own MIR body by the primary extractor (`translate_promoted_body`), and kept only when CTFE evaluates the promoted, the extraction marked nothing it could not model, and the value is closed (no placeholder variable, whose spelling is derived from the promoted body's local indices and would name one of the enclosing function's values).
//@ mechanism: here the payload read through `&Some(42)` is 42 and the contract claims 43.
//@ accept-means: the promoted's value is translated as something the program does not hold, or as a variable some other fact constrains.
//@ WHY THE CONTRACT IS FALSE: `promoted_field()` returns 42.
//@ teeth: control pair for the translation, not a regression test of a hole: rejected (`promoted_field FAILED`) with and without it. The isolating twin is promoted_const_enum_field_read_control.rs, identical but for 43, which verifies only with it.
//@ verdict: failed
//@ fn-failed: promoted_field
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 43)]
pub fn promoted_field() -> i32 {
    match &Some(42) {
        Some(v) => *v,
        None => 0,
    }
}
