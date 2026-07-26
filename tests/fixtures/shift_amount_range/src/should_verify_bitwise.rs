// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture: well-formed shifts under `#[bitwise_proof]` must VERIFY in
//! BV mode (ledger int-shift-full).
//!
//! - `shr_bitwise_guarded`: the `#[requires]` bound plus the unsigned
//!   parameter range pin the amount into `[0, 8)`, statically discharging
//!   the marker's range check in the native QF_BV lane.
//! - `shr_bitwise_masked`: the `amt & (BITS - 1)` idiom — discharged
//!   syntactically (no marker is emitted at all).

use trust_wp::{bitwise_proof, ensures, requires};

#[bitwise_proof]
#[requires(n@ < 8)]
#[ensures(result@ <= x@)]
pub fn shr_bitwise_guarded(x: u8, n: u8) -> u8 {
    x >> n
}

#[bitwise_proof]
#[ensures(result@ <= x@)]
pub fn shr_bitwise_masked(x: u8, n: u8) -> u8 {
    x >> (n & 7)
}

fn main() {
    let _ = shr_bitwise_guarded(2, 1);
    let _ = shr_bitwise_masked(2, 200);
}
