// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! proof_assert after tuple field assignment.
//!
//! Tests that projected assignments (e.g., `_3.0 = _4` in MIR) do not
//! corrupt the local expression map. Before #928, `extract_from_block_with_context`
//! would overwrite the whole local with the RHS of a field write, losing the
//! tuple context.
//!
//! Re: #928

use trust_wp::{proof_assert, requires};

/// The proof_assert depends only on the scalar argument `x`, not on
/// any tuple field write. Before #928, a field write to a local could
/// overwrite that local's expression with just the RHS, potentially
/// causing extraction to produce incorrect expressions.
#[requires(x > 0)]
fn scalar_after_tuple_field_write(x: i32) -> i32 {
    let mut pair = (0_i32, 0_i32);
    pair.0 = x;
    proof_assert!(x > 0);
    pair.0
}

fn main() {
    scalar_after_tuple_field_write(1);
}
