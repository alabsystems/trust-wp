//@ expect: reject
//@ verdict: error
//@ refused-with: as Borrow>` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: an associated type's bound written in a supertrait list (`trait Lends: Src<Out:
//@ mechanism: Borrow<i32>>`) is implied for every `T: Lends`, so a generic body borrows a `T::Out`
//@ mechanism: with no bound of its own naming one. D-193 reads a call's bounds with their traits'
//@ mechanism: supertraits (`explicit_super_predicates_of`, which holds only the `Self: Src` half) and
//@ mechanism: the bounds declared on their associated types (`type Out: Borrow<i32>`), never the
//@ mechanism: bound written on another trait's associated type in the supertrait list. `read::<M>`
//@ mechanism: asks `M: Lends`, `M: Src` and nothing else, while `M` sets `Out = Ghost<Box<i32>>`, so it
//@ mechanism: runs `<Ghost<Box<i32>> as Borrow<i32>>::borrow`, which panics. The same body with the
//@ mechanism: bound declared on `Src::Out` itself is refused at `caller`
//@ mechanism: (ghost_holder_assoc_type_bound_in_program_context_panics); only where the bound is
//@ mechanism: written differs. Found probing D-193's elaboration sideways.
//@ also-verified: read, read_dyn, <M as Src>::get
//@ fixed-by: D-194: the elaboration reads a trait's implied predicates
//@ fixed-by: (`explicit_implied_predicates_of`: its supertraits with the associated-type bounds written
//@ fixed-by: beside them), as rustc gives them to `T: Lends`.
//@ accept-means: a program body that instantiates a function at a type whose associated type is a
//@ accept-means: ghost, bounded by `Borrow` in a supertrait list, is credited `verified` and the crate
//@ accept-means: exits 0, though the call panics.
//@ WHY THE CONTRACT IS FALSE: `caller` and `caller_dyn` panic on every call ("Ghost<Box<T>>::borrow
//@ WHY THE CONTRACT IS FALSE: called at runtime"); `read` is verified against its bounds and the
//@ WHY THE CONTRACT IS FALSE: instance that breaks them is the caller's.
//@ teeth: MEASURED ACCEPTED, exit 0, on the debug driver of wp-s150 with D-193 alone: every function
//@ teeth: verified. Natively, built against trust-wp-std, `caller` exits 101 with that panic. Refused at
//@ teeth: both calls with D-194; ghost_holder_implied_assoc_type_harmless_bound_control, the same
//@ teeth: shape asking `Debug` of a ghost and `Borrow` of a `Box`, verifies with and without it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::Borrow;

pub trait Src {
    type Out;
    #[ensures(true)]
    fn get(&self) -> Self::Out;
}

pub trait Lends: Src<Out: Borrow<i32>> {}

pub struct M;

impl Src for M {
    type Out = Ghost<Box<i32>>;
    #[ensures(true)]
    fn get(&self) -> Ghost<Box<i32>> {
        ghost!(Box::new(5i32))
    }
}

impl Lends for M {}

#[ensures(result)]
pub fn read<T: Lends>(t: &T) -> bool {
    let l = t.get();
    let _v: &i32 = l.borrow();
    true
}

#[ensures(result)]
pub fn caller() -> bool {
    read(&M)
}

#[ensures(result)]
pub fn read_dyn<T: Lends>(t: &T) -> bool {
    let l = t.get();
    let d: &dyn Borrow<i32> = &l;
    let _v: &i32 = d.borrow();
    true
}

#[ensures(result)]
pub fn caller_dyn() -> bool {
    read_dyn(&M)
}
