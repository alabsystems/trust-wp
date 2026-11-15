//@ expect: reject
//@ verdict: unknown
//@ refused-with: a postcondition reads that `&mut` only through `*`, `^` or `@`
//@ mechanism: tuple_param_mut_field_postcondition_read_at_entry on a trait method with no body: the
//@ mechanism: impl that inherits the clause reads `t.0.f` at entry on both sides, so its body
//@ mechanism: obligation and its refinement against the trait's text are both discharged.
//@ accept-means: an inherited postcondition's read of a field through a `&mut` a tuple parameter holds
//@ accept-means: was placed at entry in the impl's lane.
//@ WHY THE CONTRACT IS FALSE: the clause names `t` inside `old`, so it is in the pre-Creusot dialect:
//@ WHY THE CONTRACT IS FALSE: `t.0.f` outside `old` is the value left, one more than `old(t.0.f)`.
//@ fixed-by: D-181 — the trait method's own clause is refused at discovery, so the impl inherits the
//@ fixed-by: refusal and discharges nothing.
//@ teeth: ACCEPTED (exit 0, `<A as Tr>::m verified` and its refinement verified) at the head D-181
//@ teeth: was written on.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub f: i32,
}

pub trait Tr {
    #[requires(t.0.f < 100i32)]
    #[ensures(t.0.f == old(t.0.f))]
    fn m(t: (&mut S, i32));
}

pub struct A;

impl Tr for A {
    fn m(t: (&mut S, i32)) {
        t.0.f += 1;
    }
}
