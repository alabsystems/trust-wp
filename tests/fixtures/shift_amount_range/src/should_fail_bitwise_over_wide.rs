// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture: an over-wide shift under `#[bitwise_proof]` must FAIL in
//! BV mode (ledger int-shift-full).
//!
//! The postcondition itself is VALID (`x >> n <= x` holds for every
//! unsigned pattern), so the ONLY refutable conjunct is the shift-amount
//! range obligation `0 <= n < 8` — emitted as a native BV check
//! (`bvult n, 8`) in the QF_BV proof lane. A BV encoding that treated the
//! shift-amount marker as a pure identity would falsely verify this
//! function; the Int-lane RED battery (`should_fail_unguarded`) does not
//! cover the BV lane.

use trust_wp::{bitwise_proof, ensures};

#[bitwise_proof]
#[ensures(result@ <= x@)]
pub fn shr_bitwise(x: u8, n: u8) -> u8 {
    x >> n
}

fn main() {
    let _ = shr_bitwise(1, 1);
}
