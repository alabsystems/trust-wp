//@ expect: reject
//@ mechanism: `on_assign_local` binds a destination whose right-hand side it cannot translate (here
//@ mechanism: `q as usize`, a pointer-to-integer cast) to `Var(<source name>)`. The second `let a` shadows
//@ mechanism: the first and both are bound to the one symbol `a`, so the returned value is read as the
//@ mechanism: first binding, which the early return has already shown is not 5.
//@ mechanism: the value spelling of panic_arm_guard_on_untranslated_shadowed_local.rs: no panic arm, no
//@ mechanism: cap, a postcondition over the returned binding.
//@ accept-means: a function returning `q`'s address is verified against `result != 5`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(std::ptr::null(), 5 as *const u8)` returns 5.
//@ teeth: ACCEPTED at the campaign tip, and with wp-s120's panic-arm edge credit: the symbol is shared by the extractor, not by the cap.
//@ teeth: Rejected with D-169.
//@ fixed-by: D-169 (an untranslated assignment is bound to a symbol of its own site).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ != 5)]
pub fn f(p: *const u8, q: *const u8) -> usize {
    let a = p as usize;
    if a == 5 {
        return 0;
    }
    let a = q as usize;
    a
}
