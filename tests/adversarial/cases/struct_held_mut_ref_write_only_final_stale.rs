//@ expect: reject
//@ mechanism: the isolating twin of struct_held_mut_ref_call_then_write_final_stale.rs with
//@ mechanism: the crediting call removed: the same false final-value claim about a `&mut`
//@ mechanism: held in a struct parameter, refuted by the body's own write alone. It says the
//@ mechanism: struct spelling is not itself blind to the write.
//@ accept-means: a struct-held borrow's final value could be claimed against its own write.
//@ WHY THE PROGRAM IS WRONG: the body sets `*w.r` to 2; the contract claims 1.
//@ teeth: rejected today; committed as the control on the attribution, not as a live hole.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[requires(*(w.r) == 0i32)]
#[ensures(^(w.r) == 1i32)]
pub fn f(w: W<'_>) {
    *w.r = 2i32;
}
