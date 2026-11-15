//@ expect: verify
//@ xfail: the price of D-143's opaque-binding rule: both bindings of `a` are `p`'s address, so the
//@ xfail: panic arm is dead, but a walk that bound any local to a shared opaque symbol proves no edge
//@ xfail: dead, whatever the values; `f` keeps the cap.
//@ mechanism: control twin of clause_free_panic_arm_guard_on_opaque_shadowed_local.rs, differing in
//@ mechanism: the pointer the second `a` reads.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

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
