//@ expect: reject
//@ verdict: error
//@ refused-with: as Borrow>` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: D-193 refuses a call in code that runs when a bound it asks, or one the instance must
//@ mechanism: meet to meet it, asks `Deref`, `DerefMut`, `Borrow` or `BorrowMut` of a `Ghost`. An
//@ mechanism: unsizing coercion asks the same of its source type without any call: `Box::new(g)` made a
//@ mechanism: `Box<dyn Borrow<i32>>`, `&mut g` made a `&mut dyn BorrowMut<i32>`, and `&g as &dyn
//@ mechanism: Borrow<i32>` each need `Ghost<Box<i32>>: Borrow<i32>` (or `BorrowMut`), and the later
//@ mechanism: `borrow()` through the trait object runs the ghost's own `borrow`/`borrow_mut` by its
//@ mechanism: vtable. The call is `<dyn Borrow<i32> as Borrow>::borrow`, whose self type is no ghost,
//@ mechanism: so the bound check never sees one.
//@ accept-means: a program body that turns a ghost into a trait object of `Borrow` or `BorrowMut` and
//@ accept-means: borrows through it is reported verified and exits 0, though the borrow panics.
//@ fixed-by: D-193: an unsizing coercion in code that runs asks, of the type it erases, the trait
//@ fixed-by: object's traits, elaborated and refused as a call's bounds are.
//@ WHY THE CONTRACT IS FALSE: each function panics on every call ("Ghost<Box<T>>::borrow called at
//@ WHY THE CONTRACT IS FALSE: runtime", "Ghost<Box<T>>::borrow_mut called at runtime").
//@ teeth: ACCEPTED (all three verified, exit 0) at wp-s150 70fa5356; refused with the coercion
//@ teeth: check. Natively, built against trust-wp-std, each function panics. The `dyn Deref`
//@ teeth: spelling of the same coercion was refuted (a counterexample) and is not here;
//@ teeth: ghost_unsized_to_harmless_dyn_control verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::{Borrow, BorrowMut};

#[ensures(result)]
pub fn ghost_box_dyn_borrow() -> bool {
    let g: Ghost<Box<i32>> = ghost!(Box::new(5i32));
    let d: Box<dyn Borrow<i32>> = Box::new(g);
    let _v: &i32 = (*d).borrow();
    true
}

#[ensures(result)]
pub fn ghost_ref_dyn_borrow_mut() -> bool {
    let mut g: Ghost<Box<i32>> = ghost!(Box::new(5i32));
    let d: &mut dyn BorrowMut<i32> = &mut g;
    let _v: &mut i32 = d.borrow_mut();
    true
}

#[ensures(result)]
pub fn ghost_cast_dyn_borrow() -> bool {
    let g: Ghost<Box<i32>> = ghost!(Box::new(5i32));
    let d = &g as &dyn Borrow<i32>;
    let _v: &i32 = d.borrow();
    true
}
