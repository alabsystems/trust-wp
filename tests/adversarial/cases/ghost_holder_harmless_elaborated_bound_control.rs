//@ expect: verify
//@ mechanism: the TRUE twin of ghost_holder_supertrait_bound_in_program_context_panics,
//@ mechanism: ghost_holder_blanket_impl_bound_in_program_context_panics,
//@ mechanism: ghost_holder_assoc_type_bound_in_program_context_panics and
//@ mechanism: ghost_holder_supertrait_comparison_returns_wrong_value: a ghost reaches a generic function
//@ mechanism: through a supertrait, a blanket impl's where-clause and an associated type's bound, as
//@ mechanism: there, but each of those asks `Debug` or `Clone` of it, whose run-time bodies are exact;
//@ mechanism: and a `Box` given to the `Borrow` supertrait asks `Borrow` of the `Box`, not of a ghost.
//@ mechanism: Only `Deref`, `Borrow` or a comparison reached on a ghost itself is refused.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — every function verified before and after the bounds a call asks are read through
//@ teeth: supertraits, associated types and selected impls.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::{borrow::Borrow, fmt::Debug};

pub trait Shows: Debug {}
impl<T: Debug> Shows for T {}

pub trait Dup: Clone {}
impl<T: Clone> Dup for T {}

pub trait Get {
    fn get(&self) -> i32;
}
impl<T: Debug> Get for T {
    #[ensures(true)]
    fn get(&self) -> i32 {
        0
    }
}

pub trait HasShown {
    type Shown: Debug;
}
pub struct M;
impl HasShown for M {
    type Shown = Ghost<i32>;
}

pub trait LendsI32: Borrow<i32> {}
impl<T: Borrow<i32>> LendsI32 for T {}

#[ensures(result == 0i32)]
pub fn shown<T: Shows>(_x: &T) -> i32 {
    0
}

#[ensures(result == 0i32)]
pub fn dup<T: Dup>(_x: &T) -> i32 {
    0
}

#[ensures(result == 0i32)]
pub fn has<T: Get>(_x: &T) -> i32 {
    0
}

#[ensures(result == 0i32)]
pub fn count<T: HasShown>() -> i32 {
    0
}

#[ensures(true)]
pub fn read_borrow<T: LendsI32>(x: &T) -> i32 {
    *x.borrow()
}

#[ensures(result == 0i32)]
pub fn caller() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    let a = shown(&g);
    let b = dup(&g);
    let c = has(&g);
    let d = count::<M>();
    let _e = read_borrow(&Box::new(5i32));
    a + b + c + d
}
