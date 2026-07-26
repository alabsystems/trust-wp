// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact symbolic integer bound constructors.
//!
//! Produces `PureExpr` trees for Rust integer type bounds (e.g., `u64::MAX`,
//! `i128::MIN`) using symbolic arithmetic (`2^N - 1`, `-2^(N-1)`) instead of
//! truncating to `i64`. This allows the verification encoder to represent all
//! Rust integer bounds exactly, even for types wider than 64 bits.
//!
//! These helpers are shared between the driver (for parameter range constraints)
//! and the encoder (for type constant resolution and qualified integer constants).

use std::sync::Arc;

use super::{BinOp, PureExpr};

/// Build a `PureExpr` representing `2^exp` using repeated squaring.
///
/// Keeps expression depth logarithmic in `exp` to stay well within the ay
/// encoding recursion guard (128).
#[must_use]
pub fn pow2_expr(exp: u32) -> PureExpr {
    match exp {
        0 => PureExpr::Int(1),
        1 => PureExpr::Int(2),
        _ => {
            let half = pow2_expr(exp / 2);
            let squared = PureExpr::BinOp(Arc::new(half.clone()), BinOp::Mul, Arc::new(half));
            if exp.is_multiple_of(2) {
                squared
            } else {
                PureExpr::BinOp(Arc::new(PureExpr::Int(2)), BinOp::Mul, Arc::new(squared))
            }
        }
    }
}

/// Build a `PureExpr` representing `2^bits - 1` (the max value for a
/// `bits`-wide unsigned integer). Uses a literal when the value fits in
/// `i64`, otherwise falls back to the symbolic `pow2_expr` form.
#[must_use]
pub fn unsigned_max_expr(bits: u32) -> PureExpr {
    if bits == 0 {
        return PureExpr::Int(0);
    }

    if bits <= 63 {
        let max = (1_u128 << bits) - 1;
        // SAFETY: bits <= 63 guarantees max fits in i64.
        #[allow(clippy::cast_possible_truncation)]
        return PureExpr::Int(max as i64);
    }

    PureExpr::BinOp(
        Arc::new(pow2_expr(bits)),
        BinOp::Sub,
        Arc::new(PureExpr::Int(1)),
    )
}

/// Build `(min, max)` `PureExpr`s for a `bits`-wide signed integer:
/// `(-2^(bits-1), 2^(bits-1) - 1)`.
#[must_use]
pub fn signed_bounds_expr(bits: u32) -> (PureExpr, PureExpr) {
    if bits == 0 {
        return (PureExpr::Int(0), PureExpr::Int(0));
    }

    if bits <= 63 {
        let half_range = 1_i128 << (bits - 1);
        // SAFETY: bits <= 63 guarantees both values fit in i64.
        #[allow(clippy::cast_possible_truncation)]
        return (
            PureExpr::Int((-half_range) as i64),
            PureExpr::Int((half_range - 1) as i64),
        );
    }

    if bits == 64 {
        return (PureExpr::Int(i64::MIN), PureExpr::Int(i64::MAX));
    }

    let half_range = pow2_expr(bits - 1);
    let min = PureExpr::BinOp(
        Arc::new(PureExpr::Int(0)),
        BinOp::Sub,
        Arc::new(half_range.clone()),
    );
    let max = PureExpr::BinOp(Arc::new(half_range), BinOp::Sub, Arc::new(PureExpr::Int(1)));
    (min, max)
}
