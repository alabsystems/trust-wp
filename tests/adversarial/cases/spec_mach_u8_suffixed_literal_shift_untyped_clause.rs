//@ expect: reject
//@ mechanism: `128u8 << 1u32 > 0u8` in the postcondition of a function returning `impl Sized`,
//@ mechanism: whose clause no type check reads. D-232's untyped reading takes a shift of one literal
//@ mechanism: by another as `Int` arithmetic (contract_parser::machine_arith::binary_is_int_syntax),
//@ mechanism: but `128u8` is a `u8` in the pinned oracle and the shift is the oracle's `lsl_bv`, which
//@ mechanism: drops the bit shifted past the top (D-135 item 3).
//@ accept-means: a shift of a machine-suffixed literal in a clause no type check reads was read as
//@ accept-means: a mathematical product.
//@ WHY THE CONTRACT IS FALSE: `128u8 << 1u32` shifts the only set bit out of a u8: it is 0.
//@ fixed-by: OPEN: committed RED, with spec_mach_u8_suffixed_literal_sum_untyped_clause.rs.
//@ teeth: ACCEPTED at exit 0 when written, as on the campaign base. Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(128u8 << 1u32 > 0u8)]
pub fn suffixed_literal_shift(x: u8) -> impl Sized {
    x
}
