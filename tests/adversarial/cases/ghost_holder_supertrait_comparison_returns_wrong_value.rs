//@ expect: reject
//@ verdict: error
//@ refused-with: is compared or hashed outside ghost!(...)
//@ mechanism: D-133 refuses a call whose where-clauses ask a type holding a `Ghost` for `PartialEq`,
//@ mechanism: `Ord` or `Hash`, since a ghost's own `eq` is `true` whatever the values; it reads nothing
//@ mechanism: past those where-clauses. `same<T: Same>` with `trait Same: PartialEq` asks the same of
//@ mechanism: the instance, and its `a == b` runs `<Ghost<i32> as PartialEq>::eq`, which returns `true`
//@ mechanism: for `ghost!(1)` and `ghost!(2)`. The caller is verified through `same`'s postcondition,
//@ mechanism: the logical equality of the two ghosts, which is `false`.
//@ accept-means: a program body that compares two ghosts through a function bounded by a trait whose
//@ accept-means: supertrait is `PartialEq` is credited with a postcondition its run-time result breaks.
//@ fixed-by: D-193: the holder check reads the bounds a call asks as `program_context::asked_trait_bounds`
//@ fixed-by: elaborates them, supertraits included.
//@ WHY THE CONTRACT IS FALSE: `caller` returns `true`, and its postcondition says `false`.
//@ teeth: at wp-s150 9c6178f1, `caller` verified (`same` unknown on a fail-closed `false`).
//@ teeth: Natively, built against trust-wp-std, `caller` returns `true`. Refused at wp-s150's fix;
//@ teeth: ghost_holder_harmless_elaborated_bound_control, a ghost through a `Clone` supertrait, verifies
//@ teeth: at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Same: PartialEq {}
impl<T: PartialEq> Same for T {}

#[ensures(result == (*a == *b))]
pub fn same<T: Same>(a: &T, b: &T) -> bool {
    a == b
}

#[ensures(!result)]
pub fn caller() -> bool {
    let a: Ghost<i32> = ghost!(1i32);
    let b: Ghost<i32> = ghost!(2i32);
    same(&a, &b)
}
