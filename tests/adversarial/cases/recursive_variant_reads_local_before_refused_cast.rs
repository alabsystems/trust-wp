//@ expect: reject
//@ mechanism: the recursive call-site extraction (`extract_recursive_call_args`, which the variant
//@ mechanism: decrease check reads) binds a local only when it can translate the assignment, and on an
//@ mechanism: assignment it cannot translate keeps the local's EARLIER binding: `let mut m = 0;
//@ mechanism: m = <untranslated>; spin(m, ..)` is checked as `spin(0, ..)`, and `0 < n` proves the variant
//@ mechanism: decreases. D-215 made an `f16` cast untranslated (`spin_f16`: `m = h as u32`); before it the
//@ mechanism: cast was lowered over the reals and the check was `unknown`. A float operand the operator path
//@ mechanism: does not evaluate (`spin_assoc_const`: `x + f64::EPSILON`; `spin_const_item`: `x + ONE`) leaves
//@ mechanism: the cast's operand, and so the cast, untranslated in the same way, before D-215 too.
//@ mechanism: A local shadowing a parameter is seeded with its debug name, the parameter's own symbol, so
//@ mechanism: `let b = h as u32;` untranslated is read as the parameter `b` (`spin_shadow`, `spin_shadow_f64`),
//@ mechanism: and the path condition `b < a` proves the variant decreases.
//@ mechanism: recursive_variant_reads_local_before_refused_cast_control.rs reassigns `m` from a value the
//@ mechanism: extractor translates.
//@ accept-means: `spin_f16(5, 5.0)`, `spin_assoc_const(5, 5.0)` and `spin_const_item(5, 4.0)` each call
//@ accept-means: themselves with `n == 5` forever, and `spin_shadow(10, 0, 20.0)` and
//@ accept-means: `spin_shadow_f64(10, 0, 20.0)` with `a == 20` forever; an accept claims each terminates.
//@ fixed-by: D-140 — the recursive call-site walk leaves a local unbound after an assignment it cannot
//@ fixed-by: translate or a write into part of it, so a read of it at a recursive call is refused; D-217
//@ fixed-by: translates `spin_f16`'s cast as an uninterpreted function of `h`, which proves no decrease.
//@ teeth: ACCEPTED when committed (`spin_f16`, `spin_assoc_const` and `spin_const_item` each
//@ teeth: `verified (termination)`). On the merged campaign tip before D-215 `spin_f16` was `unknown`
//@ teeth: (variant decrease) and the other two were verified. `spin_shadow` and `spin_shadow_f64` were
//@ teeth: added after, each `verified (termination)` at the same head. With the extraction leaving the
//@ teeth: local unbound, all five are FAILED (variant decrease), on the merged tip and under D-217.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]

extern crate creusot_std;

use creusot_std::prelude::*;

const ONE: f64 = 1.0;

#[check(terminates)]
#[variant(n@)]
pub fn spin_f16(n: u32, h: f16) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    m = h as u32;
    spin_f16(m, h);
}

#[check(terminates)]
#[variant(n@)]
pub fn spin_assoc_const(n: u32, x: f64) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    m = (x + f64::EPSILON) as u32;
    spin_assoc_const(m, x);
}

#[check(terminates)]
#[variant(n@)]
pub fn spin_const_item(n: u32, x: f64) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    m = (x + ONE) as u32;
    spin_const_item(m, x);
}

#[check(terminates)]
#[variant(a@)]
pub fn spin_shadow(a: u32, b: u32, h: f16) {
    if b >= a {
        return;
    }
    let b = h as u32;
    spin_shadow(b, 0, h);
}

#[check(terminates)]
#[variant(a@)]
pub fn spin_shadow_f64(a: u32, b: u32, x: f64) {
    if b >= a {
        return;
    }
    let b = (x + f64::EPSILON) as u32;
    spin_shadow_f64(b, 0, x);
}
