//@ expect: reject
//@ mechanism: the primary walk binds a local whose right-hand side has no translation (`p as usize`,
//@ mechanism: a pointer's address) to the symbol of its source name. The second assignment to `a`
//@ mechanism: binds the SAME symbol, so the path condition `!(a == 5)` read off `p`'s address is a
//@ mechanism: fact about `q`'s, and the panic arm's charge `!(a == 5)` is proved from it. D-142 read
//@ mechanism: the charged edge as dead.
//@ accept-means: a clause-free body that panics when `q`'s address is 5 is credited `verified`, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(std::ptr::null(), 5 as *const u8)` panics (a clause-free fn is checked
//@ WHY THE CONTRACT IS FALSE: under `requires true`).
//@ verdict: failed
//@ fn-failed: f
//@ teeth: MEASURED ACCEPTED under D-142 before D-143: `f verified`, exit 0.
//@ teeth: Rejected once an opaque binding in the walk proves no edge dead
//@ teeth: (`panic_site_coverage::record_opaque_binding`).
//@ teeth: With D-169 the charge itself is refuted, so `f FAILED` before any cap is read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

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
