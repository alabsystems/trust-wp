//@ expect: reject
//@ mechanism: the shadowing spelling of clause_free_panic_arm_guard_on_opaque_rebinding.rs: two MIR
//@ mechanism: locals named `a`, each bound to an untranslated address, share the symbol `a`.
//@ accept-means: a clause-free body that panics when `q`'s address is 5 is credited `verified`, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(std::ptr::null(), 5 as *const u8)` panics (a clause-free fn is checked
//@ WHY THE CONTRACT IS FALSE: under `requires true`).
//@ verdict: failed
//@ fn-failed: f
//@ teeth: MEASURED ACCEPTED under D-142 before D-143: `f verified`, exit 0.
//@ teeth: With D-169 the charge itself is refuted, so `f FAILED` before any cap is read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn f(p: *const u8, q: *const u8) {
    let a = p as usize;
    if a == 5 {
        return;
    }
    let a = q as usize;
    if a == 5 {
        panic!()
    }
}
