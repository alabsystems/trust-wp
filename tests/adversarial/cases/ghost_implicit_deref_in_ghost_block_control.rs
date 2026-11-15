//@ expect: verify
//@ mechanism: the TRUE twin of ghost_implicit_deref_in_program_context_panics: the same coercion,
//@ mechanism: field read and method call, inside `ghost!`, which is erased at run time.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified`, exit 0, when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() {
    let g = ghost!(5i32);
    let p = ghost!((5i32, 6i32));
    ghost! {
        let r: &i32 = &g;
        let m = g.abs();
        proof_assert!(*r == 5);
        proof_assert!(p.0 == 5);
        proof_assert!(m == 5);
    };
}
