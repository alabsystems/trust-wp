// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Soundness regression (adjudicated 2026-07-22, dn33-39 class).
//!
//! The block extractor's per-path write facts for `*ma += 2` used collapsed
//! naming; on the no-swap path (`*ma >= *mb >= *mc` at entry) the fact
//! degenerated to the contradiction `*ma == *ma + 2`, asserting the negation
//! of that REACHABLE path condition. This program's postcondition
//! (`result == (*ma < *mb || *mb < *mc)` at entry, claimed `true`) is false
//! exactly on that path — e.g. inputs (5, 3, 1) — so it MUST fail. Before
//! the fix it falsely verified.

#![allow(unexpected_cfgs)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(^mma == *mmb && ^mmb == *mma)]
fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32) {
    std::mem::swap(mma, mmb);
}

#[requires(*ma <= 1_000_000u32 && *mb <= 1_000_000u32 && *mc <= 1_000_000u32)]
#[ensures(result)]
fn entry_order_claim<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32, mut mc: &'a mut u32) -> bool {
    let r = *ma < *mb || *mb < *mc;
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    if *mb < *mc {
        swap(&mut mb, &mut mc);
    }
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    *ma += 2;
    *mb += 1;
    r
}

fn main() {
    // Witness of the postcondition violation: no-swap path, r == false.
    let (mut a, mut b, mut c) = (5u32, 3u32, 1u32);
    let _ = entry_order_claim(&mut a, &mut b, &mut c);
}
