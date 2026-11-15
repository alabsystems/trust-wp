//@ expect: reject
//@ verdict: error
//@ refused-with: as std::ops::Add>` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: a bound that asks `Int` for a trait with no method of its own is read as running nothing,
//@ mechanism: though the trait's supertrait is `Add`: `dbl<T: Num>` with `trait Num: Add<Output = Self>`
//@ mechanism: reads `x + x` as a call with no precondition, and given `Int` its body runs
//@ mechanism: `<Int as Add>::add` on the host `i128`, which overflows past `i128::MAX`. The caller is
//@ mechanism: credited, though the call panics.
//@ accept-means: a program body that hands `Int`s to a function bounded by a trait whose supertrait is
//@ accept-means: `Add` is credited `verified`, though the call panics.
//@ fixed-by: D-193: the bounds a call asks are read with their supertraits
//@ fixed-by: (`program_context::asked_trait_bounds`), so `Int: Num` asks `Int: Add`.
//@ WHY THE CONTRACT IS FALSE: `caller` panics on every call ("attempt to add with overflow").
//@ teeth: at wp-s150 9c6178f1, `caller` verified (`dbl` FAILED on its generic `x + x`).
//@ teeth: Natively, against the campaign's debug trust-wp-std, `caller` panics in `<Int as Add>::add`.
//@ teeth: Refused at wp-s150's fix; logic_int_structural_supertrait_control, `Int` through a trait whose
//@ teeth: supertraits are `Ord` and `Copy`, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::ops::Add;

pub trait Num: Add<Output = Self> + Copy {}
impl<T: Add<Output = T> + Copy> Num for T {}

#[ensures(true)]
pub fn dbl<T: Num>(x: T) -> T {
    x + x
}

#[ensures(true)]
pub fn caller() -> bool {
    let _c = dbl(Int(i128::MAX));
    true
}
