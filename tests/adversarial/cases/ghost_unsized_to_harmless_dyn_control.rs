//@ expect: verify
//@ mechanism: control for ghost_unsized_to_dyn_borrow_in_program_context_panics. Unsizing a ghost to a
//@ mechanism: trait object whose traits run nothing of the ghost's (`Debug` prints a constant), a
//@ mechanism: holder of a ghost to `dyn Deref` (the `Box` derefs to the ghost without running it), and a
//@ mechanism: closure to `dyn Fn` are each left to the program; the refusal is for the ghost's own
//@ mechanism: `Deref`, `DerefMut`, `Borrow` and `BorrowMut` only.
//@ accept-means: n/a (control) — every contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — natively each function returns its value; verified before and after the coercion
//@ teeth: check.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::fmt::Debug;
use std::ops::Deref;

#[ensures(result)]
pub fn ghost_to_dyn_debug() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let _d: Box<dyn Debug> = Box::new(g);
    true
}

#[ensures(result)]
pub fn ghost_holder_to_dyn_deref() -> bool {
    let h: Box<Ghost<i32>> = Box::new(ghost!(5i32));
    let _d: &dyn Deref<Target = Ghost<i32>> = &h;
    true
}

#[ensures(result == 3i32)]
pub fn closure_to_dyn_fn() -> i32 {
    let f: &dyn Fn(i32) -> i32 = &|x: i32| x;
    let _ = f;
    3i32
}
