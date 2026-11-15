//@ expect: reject
//@ mechanism: `255u8 + 1u8 > 255u8` in a closure contract of two attributes, which the type-check
//@ mechanism: vehicle never reads (D-232's untyped reading): the operator on two literals is taken as
//@ mechanism: `Int` arithmetic although `255u8` is a `u8` in the pinned oracle and the sum wraps.
//@ accept-means: an operator on two machine-suffixed literals in a closure contract no type check
//@ accept-means: reads was read as mathematical integer arithmetic.
//@ WHY THE CONTRACT IS FALSE: the wrapping sum of 255u8 and 1u8 is 0, which is not above 255.
//@ fixed-by: OPEN: committed RED, with spec_mach_u8_suffixed_literal_sum_untyped_clause.rs.
//@ also-verified: suffixed_literal_closure
//@ teeth: `suffixed_literal_closure::{closure#0} verified` at exit 0 when written, as on the campaign
//@ teeth: base. Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn suffixed_literal_closure() {
    let c = #[requires(true)]
    #[ensures(255u8 + 1u8 > 255u8)]
    |x: u8| x;
    let _ = c(1);
}
