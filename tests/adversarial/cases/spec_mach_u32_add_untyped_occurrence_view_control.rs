//@ expect: verify
//@ mechanism: control for spec_mach_u32_add_untyped_occurrence_of_a_typed_text: the same two
//@ mechanism: occurrences of one text, typed and untyped, with every operand an `@` view, which
//@ mechanism: is an `Int` at any type, so both read mathematically.
//@ WHY THE CONTRACT IS TRUE: a view of an unsigned integer is at least 0, so adding b@ to a@ never
//@ WHY THE CONTRACT IS TRUE: goes below a@.
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(a@ + b@ >= a@)]
pub fn typed_u64(a: u64, b: u64) {}

#[ensures(a@ + b@ >= a@)]
pub fn untyped_u32(a: u32, b: u32) -> impl Sized {
    0u8
}
