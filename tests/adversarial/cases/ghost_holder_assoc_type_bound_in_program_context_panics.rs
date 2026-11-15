//@ expect: reject
//@ verdict: error
//@ refused-with: as Borrow>` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: a trait's associated type can carry a bound (`type Lender: Borrow<i32>`) that a generic
//@ mechanism: body uses on a value of that type. `read<T: HasLender>` asks only `T: HasLender`, which
//@ mechanism: names no ghost; the instance `M` sets `Lender = Ghost<Box<i32>>`, so `read::<M>` runs
//@ mechanism: `<Ghost<Box<i32>> as Borrow<i32>>::borrow`, which panics. The call site owes the bounds
//@ mechanism: of the associated types its instance fixes.
//@ accept-means: a program body that instantiates a function at a type whose associated type is a ghost
//@ accept-means: bounded by `Borrow` is credited `verified`, though the call panics.
//@ fixed-by: D-193: the bounds a call asks are read with those of their traits' associated types, as
//@ fixed-by: the instance fixes them (`program_context::asked_trait_bounds`).
//@ WHY THE CONTRACT IS FALSE: `caller` panics on every call ("Ghost<Box<T>>::borrow called at
//@ WHY THE CONTRACT IS FALSE: runtime").
//@ teeth: at wp-s150 7312df2a, `caller` verified (`read` unknown on a fail-closed `false`).
//@ teeth: Natively, built against trust-wp-std, `caller` panics in `read`. Refused at wp-s150's fix;
//@ teeth: ghost_holder_harmless_elaborated_bound_control, an associated ghost type bounded by `Debug`,
//@ teeth: verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::Borrow;

pub trait HasLender {
    type Lender: Borrow<i32>;
    fn lender() -> Self::Lender;
}

pub struct M;

impl HasLender for M {
    type Lender = Ghost<Box<i32>>;
    fn lender() -> Ghost<Box<i32>> {
        ghost!(Box::new(5i32))
    }
}

#[ensures(true)]
pub fn read<T: HasLender>() -> i32 {
    let l = T::lender();
    *l.borrow()
}

#[ensures(true)]
pub fn caller() -> i32 {
    read::<M>()
}
