//@ expect: verify
//@ mechanism: the boundary of tuple_param_struct_held_mut_postcondition_read_at_entry: a `requires`
//@ mechanism: reads the `&mut` `t` holds through `W`'s field at entry, and the postcondition reads
//@ mechanism: only the value beside it. D-181 makes `t` `HeldMutable`, which refuses postcondition
//@ mechanism: reads through the `&mut` alone.
//@ teeth: n/a — over-refusal control; verifies with D-181 and without it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[requires(*t.0.r < 100i32)]
#[ensures(result == t.1)]
pub fn f(t: (W, i32)) -> i32 {
    t.1
}
