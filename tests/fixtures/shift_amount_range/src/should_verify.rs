// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture: well-formed shifts must still VERIFY.
//!
//! Three provable range shapes (ledger int-shift-full):
//! - an in-range literal amount (`x >> 3`) — discharged syntactically,
//! - the `amt & (BITS - 1)` masking idiom — discharged syntactically,
//! - a `#[requires]`-guarded symbolic amount — discharged by the solver
//!   from the precondition plus the unsigned parameter range.

use trust_wp::{ensures, requires};

#[ensures(true)]
pub fn shr_literal(x: u8) -> u8 {
    x >> 3
}

#[ensures(true)]
pub fn shl_masked(x: u8, n: u8) -> u8 {
    x << (n & 7)
}

#[requires(n@ < 8)]
#[ensures(true)]
pub fn shr_guarded(x: u8, n: u8) -> u8 {
    x >> n
}

fn main() {
    let _ = shr_literal(8);
    let _ = shl_masked(1, 200);
    let _ = shr_guarded(2, 1);
}
