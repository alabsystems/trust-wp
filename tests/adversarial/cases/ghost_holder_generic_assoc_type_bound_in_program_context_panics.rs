//@ expect: reject
//@ mechanism: a generic associated type's bound (`type Lender<'a>: Borrow<i32> where Self: 'a`) is
//@ mechanism: what a generic body borrows a `T::Lender<'_>` by. D-193 reads the bounds of a trait's
//@ mechanism: associated types as the instance fixes them, but skips every associated type with
//@ mechanism: parameters of its own (`own_params` non-empty in `elaborate_asked_bounds`), since the
//@ mechanism: trait's arguments do not instantiate them. `read::<M>` asks only `M: HasLender`, while
//@ mechanism: `M` sets `Lender<'a> = Ghost<Box<i32>>`, so it runs `<Ghost<Box<i32>> as
//@ mechanism: Borrow<i32>>::borrow`, which panics. The plain associated type with the same bound is
//@ mechanism: refused at `caller` (ghost_holder_assoc_type_bound_in_program_context_panics). Found
//@ mechanism: probing D-193's elaboration sideways.
//@ also-verified: read, <M as HasLender>::lender
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a generic associated type's
//@ fixed-by: bounds are read at the instance (its own lifetimes erased), and a call is refused where
//@ fixed-by: they cannot be instantiated, rather than skipped.
//@ accept-means: a program body that instantiates a function at a type whose generic associated type
//@ accept-means: is a ghost bounded by `Borrow` is credited `verified` and the crate exits 0, though
//@ accept-means: the call panics.
//@ WHY THE CONTRACT IS FALSE: `caller` panics on every call ("Ghost<Box<T>>::borrow called at
//@ WHY THE CONTRACT IS FALSE: runtime"); `read` is verified against its bounds and the instance that
//@ WHY THE CONTRACT IS FALSE: breaks them is the caller's.
//@ teeth: MEASURED ACCEPTED, exit 0, on the debug driver of wp-s150 with D-193: every function
//@ teeth: verified. Natively, built against trust-wp-std, `caller` exits 101 with that panic. The campaign
//@ teeth: tip has no check that reads a call's bounds, so nothing there refuses it either (not run).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::Borrow;

pub trait HasLender {
    type Lender<'a>: Borrow<i32>
    where
        Self: 'a;
    #[ensures(true)]
    fn lender(&self) -> Self::Lender<'_>;
}

pub struct M;

impl HasLender for M {
    type Lender<'a> = Ghost<Box<i32>>;
    #[ensures(true)]
    fn lender(&self) -> Ghost<Box<i32>> {
        ghost!(Box::new(5i32))
    }
}

#[ensures(result)]
pub fn read<T: HasLender>(t: &T) -> bool {
    let l = t.lender();
    let _v: &i32 = l.borrow();
    true
}

#[ensures(result)]
pub fn caller() -> bool {
    read(&M)
}
