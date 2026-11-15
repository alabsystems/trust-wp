//@ expect: reject
//@ verdict: error
//@ refused-with: `Ghost::into_inner` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: `Ghost::inner` and `Ghost::into_inner` panic at run time. Program code that calls one is
//@ mechanism: refused, but the extraction check looks only at a call's callee (`is_ghost_extraction_callee`)
//@ mechanism: and a method call, and D-193's list of trust-wp-std inherent methods a program may not
//@ mechanism: run, which does see a function named as a value (`call_instantiation`), names only
//@ mechanism: `Ghost::clone` among `Ghost`'s. Named as a value and handed to `Option::map`, either runs
//@ mechanism: inside `map` where no check looks. Found probing D-193's value-position reading sideways.
//@ fixed-by: D-194: `Ghost::inner`, `inner_mut` and `into_inner` join `Ghost::clone` in
//@ fixed-by: `program_context::divergent_inherent_method`, which reads a function named as a value as
//@ fixed-by: it reads a call.
//@ accept-means: a program body that extracts a ghost's value through `Option::map` is credited
//@ accept-means: `verified`, though the extraction panics.
//@ WHY THE CONTRACT IS FALSE: each function panics on every call ("Ghost::inner called at runtime",
//@ WHY THE CONTRACT IS FALSE: "Ghost::into_inner called at runtime").
//@ teeth: MEASURED ACCEPTED, exit 0, on the debug driver of wp-s150 with D-193 alone: both functions
//@ teeth: verified. The same shape through `Ghost::inner_mut` is withdrawn on its `&mut` handed to
//@ teeth: `map`, so it is not here. Natively, built against trust-wp-std, each function exits 101 with
//@ teeth: its panic. Refused at both with D-194; ghost_holder_implied_assoc_type_harmless_bound_control
//@ teeth: hands `Ghost::borrow`, the zero-sized handle, to `map` and verifies with and without it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn map_inner() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let _r: Option<&i32> = Some(&g).map(Ghost::inner);
    true
}

#[ensures(result)]
pub fn map_into_inner() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let _r: Option<i32> = Some(g).map(Ghost::into_inner);
    true
}
