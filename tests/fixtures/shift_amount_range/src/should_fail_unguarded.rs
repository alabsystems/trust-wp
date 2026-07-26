// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test fixture: a symbolic shift amount with no range guard must FAIL.
//!
//! No precondition bounds `n`, so the `0 <= n < 8` obligation emitted by
//! the shift lowering is unprovable (counterexample: n = 8).
//! (ledger int-shift-full)

use trust_wp::ensures;

#[ensures(true)]
pub fn shr_unguarded(x: u8, n: u8) -> u8 {
    x >> n
}

fn main() {
    let _ = shr_unguarded(1, 1);
}
