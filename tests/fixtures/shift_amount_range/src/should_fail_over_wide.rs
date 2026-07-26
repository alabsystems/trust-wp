// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture: an over-wide literal shift must FAIL verification.
//!
//! The int-shift-full shape (ledger int-shift-full): `1u8 >> 8` shifts an
//! 8-bit value by 8, which is an overflow panic at runtime. The shift
//! lowering emits the `0 <= amount < 8` range obligation, which is
//! unsatisfiable for amount = 8, so verification must fail — previously the
//! missing obligation let this function verify (a false proof).

use trust_wp::ensures;

/// The trivially-true postcondition must NOT let the unsafe shift through:
/// body side obligations are proved even when no postcondition needs them.
#[allow(arithmetic_overflow)]
#[ensures(true)]
pub fn shr_full() -> u8 {
    1u8 >> 8
}

fn main() {
    // Not executed by the test (compile/verify only); the call would panic.
    let _ = shr_full;
}
