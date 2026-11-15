//@ expect: verify
//@ mechanism: the TRUE twin of ghost_holder_supertrait_assoc_type_bound_in_program_context_panics and
//@ mechanism: ghost_extraction_named_as_value_in_program_context_panics. A ghost reaches a generic
//@ mechanism: function as the associated type a supertrait list bounds (`trait Shows: Src<Out:
//@ mechanism: Debug>`), as there, but that bound asks `Debug` of it, whose run-time body is exact; a
//@ mechanism: `Box` set as the associated type `Lends: Src<Out: Borrow<i32>>` bounds is asked `Borrow`
//@ mechanism: itself, not a ghost; and `Ghost::borrow`, named as a value and handed to `Option::map`,
//@ mechanism: is the zero-sized ghost handle at run time. Only `Deref`, `Borrow` or a comparison
//@ mechanism: reached on a ghost, or a `Ghost` method that panics, is refused.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — every function verified with and without the implied associated-type bounds
//@ teeth: and `Ghost::inner`, `inner_mut` and `into_inner` read by D-193's checks.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::{borrow::Borrow, fmt::Debug};

pub trait Src {
    type Out;
    #[ensures(true)]
    fn get(&self) -> Self::Out;
}

pub trait Shows: Src<Out: Debug> {}
pub trait Lends: Src<Out: Borrow<i32>> {}

pub struct G;
impl Src for G {
    type Out = Ghost<i32>;
    #[ensures(true)]
    fn get(&self) -> Ghost<i32> {
        ghost!(5i32)
    }
}
impl Shows for G {}

pub struct B;
impl Src for B {
    type Out = Box<i32>;
    #[ensures(true)]
    fn get(&self) -> Box<i32> {
        Box::new(5i32)
    }
}
impl Lends for B {}

#[ensures(result)]
pub fn shown<T: Shows>(t: &T) -> bool {
    let _o = t.get();
    true
}

#[ensures(result)]
pub fn lent<T: Lends>(t: &T) -> bool {
    let o = t.get();
    let _v: &i32 = o.borrow();
    true
}

#[ensures(result)]
pub fn caller() -> bool {
    shown(&G) && lent(&B)
}

#[ensures(result)]
pub fn map_ghost_borrow() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let _r: Option<Ghost<&i32>> = Some(&g).map(Ghost::borrow);
    true
}
