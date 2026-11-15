//@ expect: reject
//@ mechanism: `on_assign_local` bound a destination whose right-hand side it cannot translate (here
//@ mechanism: `q as usize`, a pointer-to-integer cast) to `Var(<source name>)`. `a` is reassigned, not
//@ mechanism: shadowed: one local, two assignment sites, one symbol, so the early return's path guard
//@ mechanism: `!(a == 5)` about the first value discharged the panic goal about the second. The symbol now
//@ mechanism: names the assignment site (`untranslated_assignment_symbol`, D-169).
//@ accept-means: a body that panics when `q`'s address is 5 is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(std::ptr::null(), 5 as *const u8)` panics, and a function with a contract
//@ WHY THE CONTRACT IS FALSE: must not panic.
//@ teeth: ACCEPTED before D-169; rejected with it.
//@ fixed-by: D-169 (an untranslated assignment is bound to a symbol of its own site).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(p: *const u8, q: *const u8) {
    let mut a = p as usize;
    if a == 5 {
        return;
    }
    a = q as usize;
    if a == 5 {
        panic!()
    }
}
