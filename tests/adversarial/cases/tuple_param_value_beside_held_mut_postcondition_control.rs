//@ expect: verify
//@ mechanism: the boundary of tuple_param_mut_field_postcondition_read_at_entry: a postcondition
//@ mechanism: reads the value a tuple parameter holds beside its `&mut` (`t.1`), a field of that
//@ mechanism: value (`u.1.v`) and a field through a shared reference beside it (`w.0.f`). None of
//@ mechanism: them reaches a `&mut`, so D-181's discovery check leaves each read at entry.
//@ teeth: n/a — over-refusal control; verifies with D-181 and without it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub v: i32,
}

pub struct S {
    pub f: i32,
}

#[requires(*t.0 < 100i32 && t.1 > 0i32)]
#[ensures(t.1 > 0i32)]
pub fn value_beside(t: (&mut i32, i32)) {
    *t.0 += 1;
}

#[requires(*u.0 < 100i32 && u.1.v > 0i32)]
#[ensures(u.1.v > 0i32)]
pub fn value_field_beside(u: (&mut i32, P)) {
    *u.0 += 1;
}

#[requires(*w.1 < 100i32 && w.0.f > 0i32)]
#[ensures(w.0.f > 0i32)]
pub fn shared_field_beside(w: (&S, &mut i32)) {
    *w.1 += 1;
}
