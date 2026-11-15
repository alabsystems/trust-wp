//@ expect: verify
//@ xfail: capped by D-143: the walk bound a local to an untranslated value (`record_opaque_binding`), so
//@ xfail: D-142's proved edge does not leave the cap: `f unknown (partial: panic paths unchecked (panic
//@ xfail: call))`. D-169's value symbol makes the two casts one value; retire this when a decision lifts
//@ xfail: D-143's opaque-binding rule for the symbols D-169 gives.
//@ mechanism: `on_assign_local` binds a destination whose right-hand side it cannot translate (a
//@ mechanism: pointer-to-integer cast) to a symbol of its site, or of its value when that value is fixed for
//@ mechanism: the execution (`untranslated_value_key`), never to `Var(<source name>)`.
//@ mechanism: control: both bindings cast the SAME parameter `p`, which is never reassigned nor written
//@ mechanism: behind the walk's back, so both casts are one value symbol and the early return does exclude
//@ mechanism: the panic. Twin of panic_arm_guard_on_untranslated_shadowed_local.rs,
//@ mechanism: whose second cast reads `q`, another value.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(p: *const u8) {
    let a = p as usize;
    if a == 5 {
        return;
    }
    let a = p as usize;
    if a == 5 {
        panic!()
    }
}
