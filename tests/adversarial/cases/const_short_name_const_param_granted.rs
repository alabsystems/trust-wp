//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__N` was not resolved to one definition by the driver
//@ mechanism: inside `f` the bare name `N` is its const generic parameter, which shadows the
//@ mechanism: constant item `N` (0); the substitution table replaced it with the item's value, so
//@ mechanism: `N == 0` read `0 == 0` and `f` verified for every `N`.
//@ accept-means: `f` claims `N == 0` for every `N`; `f::<3>` is callable.
//@ fixed-by: D-111 (a bare constant name the crate gives more than one meaning is refused wherever the table substitutes it)
//@ teeth: MEASURED before D-111: ACCEPTED, exit 0, `f verified ✓`. At the fix every clause spelling the name is refused and no function in the crate is credited on it; const_short_name_unique_control.rs, one constant spelled everywhere, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub const N: usize = 0;

#[ensures(N == 0usize)]
pub fn f<const N: usize>() {}
