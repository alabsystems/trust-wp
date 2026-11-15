//@ expect: reject
//@ mechanism: a promoted constant CTFE cannot hand back as a scalar or a newtype (`&Some(42)`, `&(3, 4)`) is read off the promoted's own MIR body by the primary extractor (`translate_promoted_body`), and kept only when CTFE evaluates the promoted, the extraction marked nothing it could not model, and the value is closed (no placeholder variable, whose spelling is derived from the promoted body's local indices and would name one of the enclosing function's values).
//@ mechanism: here the fields read through `&(3, 4)` sum to 7 and the contract claims 8.
//@ accept-means: the promoted's value is translated as something the program does not hold, or as a variable some other fact constrains.
//@ WHY THE CONTRACT IS FALSE: `promoted_pair()` returns 7.
//@ teeth: control pair for the translation, not a regression test of a hole: rejected with and without it (`FAILED` over the unconstrained placeholder without it; with it the refutation is withheld as `unknown`, exactly as for the same tuple held in a local). The isolating twin is promoted_const_tuple_field_read_control.rs, identical but for 7.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 8)]
pub fn promoted_pair() -> i32 {
    let p: &(i32, i32) = &(3, 4);
    p.0 + p.1
}
