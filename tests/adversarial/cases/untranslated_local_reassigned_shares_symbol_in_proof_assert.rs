//@ expect: reject
//@ mechanism: `on_assign_local` bound a destination whose right-hand side it cannot translate (here
//@ mechanism: `q as usize`, a pointer-to-integer cast) to `Var(<source name>)`. `a` is reassigned, so the
//@ mechanism: `proof_assert!` about its second value was proved from the early return's guard about its
//@ mechanism: first. The proof_assert spelling of untranslated_local_reassigned_shares_symbol_panic_arm.rs.
//@ accept-means: an assertion that is false when `q`'s address is 5 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(std::ptr::null(), 5 as *const u8)` reaches the assertion with `a == 5`.
//@ teeth: ACCEPTED before D-169; rejected with it.
//@ fixed-by: D-169 (an untranslated assignment is bound to a symbol of its own site).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(p: *const u8, q: *const u8) {
    let mut a = p as usize;
    if a == 5 {
        return;
    }
    a = q as usize;
    proof_assert!(a@ != 5);
}
