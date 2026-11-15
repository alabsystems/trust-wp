// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: bodies whose arithmetic obligations are stated by the conservative
//! region walks (a CFG cycle or a write through a borrow) still discharge
//! them when the facts hold on every path.

use trust_wp::ensures;

/// No invariant: the pre-loop `k + 1` is stated by the exact entry-region
/// walk (the primary extractor defers bodies with a CFG cycle).
#[ensures(true)]
pub fn before_loop(n: u8) -> u8 {
    let k: u8 = 7;
    let base = k + 1;
    let mut i: u8 = 0;
    while i < n {
        i += 1;
    }
    let _ = i;
    base
}

/// Loop body arithmetic guarded by the loop condition (no invariant).
#[ensures(true)]
pub fn guarded_in_loop(n: u8) -> u8 {
    let mut i: u8 = 0;
    while i < n {
        i += 1;
    }
    i
}

/// A write through a borrow of an unrelated local does not stop a
/// constant-operand obligation.
#[ensures(true)]
pub fn ref_unrelated(y: u8) -> u8 {
    let mut v: u8 = 0;
    let r = &mut v;
    *r = y;
    let c: u8 = 3;
    c + 4
}

fn main() {}
