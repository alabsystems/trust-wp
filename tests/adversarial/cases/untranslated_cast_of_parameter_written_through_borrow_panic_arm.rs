//@ expect: reject
//@ mechanism: an assignment the walk cannot translate (a pointer-to-integer cast) is bound to a symbol of
//@ mechanism: its site, or of its value when that value is fixed for the execution
//@ mechanism: (`untranslated_value_key`): a cast of a parameter that is never reassigned nor written behind
//@ mechanism: the walk's back. Here `p` is written through a `&mut` borrow between the two casts, a write
//@ mechanism: the walk does not see, so the casts compute two values and must be two symbols.
//@ accept-means: a clause-free body that panics when `q`'s address is 5 is credited `verified`, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(std::ptr::null(), 5 as *const u8)` panics (a clause-free fn is checked
//@ WHY THE CONTRACT IS FALSE: under `requires true`).
//@ teeth: accepted if a cast of a parameter lent `&mut` were keyed by the parameter alone.
//@ fixed-by: D-169 (an untranslated assignment is bound to a symbol of its own site unless its value is
//@ fixed-by: fixed for the execution).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(mut p: *const u8, q: *const u8) {
    let a = p as usize;
    if a == 5 {
        return;
    }
    let r = &mut p;
    *r = q;
    let a = p as usize;
    if a == 5 {
        panic!()
    }
}
