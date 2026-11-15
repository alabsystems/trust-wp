//@ expect: reject
//@ mechanism: the `match` spelling of v7_closure_let_alias_old_view: `match p { q => .. }` over a
//@ mechanism: closure's `&mut` parameter, read under `old(q@)`.
//@ accept-means: `q@ == old(q@)` holds of a closure that increments `*p`.
//@ WHY THE CONTRACT IS FALSE: `q` is `p`, named inside `old`, so `q@` outside it is entry + 1.
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
    #[ensures(match p { q => old(q@) == q@ })]
    |p: &mut u32| {
        *p += 1;
    };
    let mut z = 1u32;
    c(&mut z);
}
