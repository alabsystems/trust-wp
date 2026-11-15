//@ expect: reject
//@ verdict: unknown
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: a postcondition reads a field of a `&mut` a destructuring parameter binds, through
//@ mechanism: Rust's auto-deref (`p.f` of `(p, q): (&mut S, &mut S)`), not through `*`, `^` or `@`.
//@ mechanism: Stated over the projection alone it is `(__twp_arg0.0).f`, the read the tuple lane makes
//@ mechanism: of `t.0.f`, at entry (tuple_param_mut_field_postcondition_read_at_entry).
//@ accept-means: a postcondition read of a destructured `&mut`'s referent was placed at entry, in the
//@ accept-means: dialect whose read outside `old` is the value it is left with.
//@ WHY THE CONTRACT IS FALSE: the clause names `p`, which holds a `&mut`, inside `old`, so it is in
//@ WHY THE CONTRACT IS FALSE: the pre-Creusot dialect: `p.f` outside `old` is the value left, one more
//@ WHY THE CONTRACT IS FALSE: than `old(p.f)`.
//@ fixed-by: D-179 — a postcondition reads a `&mut` a pattern binds only through `*`, `^` or `@`,
//@ fixed-by: each refused by D-101's rule; any other read of it is refused at discovery.
//@ teeth: ACCEPTED (exit 0, `g verified`) with D-179's projection and the discovery-time read check
//@ teeth: ablated (measured in place on D-179's code commit); the twin `p.f == old(p.f) + 1` is FAILED
//@ teeth: there, so the ablated lane reads `p.f` at entry, as the tuple twin
//@ teeth: tuple_param_mut_field_postcondition_read_at_entry does at this head.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub f: i32,
}

#[requires(p.f < 100i32)]
#[ensures(p.f == old(p.f))]
pub fn g((p, _q): (&mut S, &mut S)) {
    p.f += 1;
}
