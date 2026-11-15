//@ expect: reject
//@ mechanism: `exists<c: char> (c as u32)@ > 1114111`: no `char` is past 0x10FFFF, so the claim is false.
//@ mechanism: D-203 states a binder's range only where its written type is a machine integer
//@ mechanism: (`quantifiers::binder_range`); a `char` binder gets none, and `c as u32` keeps the binder's
//@ mechanism: unbounded integer value, so the solver finds a witness past every scalar value. A program
//@ mechanism: `char` parameter is not read this way (its cast is not proved past 0x10FFFF).
//@ fixed-by: OPEN — committed RED rather than hidden. Closes where a `char` binder ranges over the
//@ fixed-by: scalar values (or is refused, as D-203 refuses a binder whose range it cannot state).
//@ accept-means: a function is credited with `exists<c: char> (c as u32)@ > 1114111` and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`char_above verified ✓`) with D-203's binder ranges and at the
//@ teeth: campaign tip this branch was built on alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// WRONG: no `char` exceeds 0x10FFFF.
#[ensures(exists<c: char> (c as u32)@ > 1114111)]
pub fn char_above() {}
