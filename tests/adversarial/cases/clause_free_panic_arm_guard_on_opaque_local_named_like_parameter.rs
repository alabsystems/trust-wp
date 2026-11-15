//@ expect: reject
//@ mechanism: the parameter spelling of clause_free_panic_arm_guard_on_opaque_rebinding.rs: the local
//@ mechanism: `a` bound to `q`'s untranslated address shares the symbol `a` with the parameter `a`,
//@ mechanism: so the path condition `!(a == 5)` on the parameter proves the panic arm's charge.
//@ accept-means: a clause-free body that panics when `q`'s address is 5 is credited `verified`, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(0, 5 as *const u8)` panics (a clause-free fn is checked under
//@ WHY THE CONTRACT IS FALSE: `requires true`).
//@ verdict: failed
//@ fn-failed: f
//@ teeth: MEASURED ACCEPTED under D-142 before D-143: `f verified`, exit 0.
//@ teeth: With D-169 the charge itself is refuted, so `f FAILED` before any cap is read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn f(a: usize, q: *const u8) {
    if a == 5 {
        return;
    }
    let a = q as usize;
    if a == 5 {
        panic!()
    }
}
