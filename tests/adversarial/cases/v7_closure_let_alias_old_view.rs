//@ expect: reject
//@ mechanism: a closure contract binds its `&mut` parameter (`let q = p`) and reads it under
//@ mechanism: `old(q@)`. The parser keeps that `let` (under `old` a name is read in the entry
//@ mechanism: state), and the driver's parameter alias resolution and placement refusal
//@ mechanism: (D-100) return early for a closure, so the name-keyed dialect check sees no `&mut`
//@ mechanism: parameter inside `old` and reads `q@` outside it as the entry value.
//@ accept-means: `q@ == old(q@)` holds of a closure that increments `*p`.
//@ WHY THE CONTRACT IS FALSE: the clause reaches `p` inside `old` (contract-syntax.md: "however the
//@ WHY THE CONTRACT IS FALSE: text reaches v: through a binder (let q = v)"), so `q@` outside `old` is
//@ WHY THE CONTRACT IS FALSE: the value `p` is left with, entry + 1.
//@ fixed-by: D-101 (a closure's parameters are read through the state elaboration a function's are)
//@ teeth: MEASURED on d73d0571 (debug driver): `host::{closure#0} verified`. On the D-101
//@ teeth: tree: unknown; the true twin (tests/fixtures/state_elaboration
//@ teeth: closure_contracts_true) verifies there.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![feature(stmt_expr_attributes, proc_macro_hygiene)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn host() {
    let c = #[requires((*p)@ < 100)]
    #[ensures({ let q = p; old(q@) == q@ })]
    |p: &mut u32| {
        *p += 1;
    };
    let mut z = 1u32;
    c(&mut z);
}
