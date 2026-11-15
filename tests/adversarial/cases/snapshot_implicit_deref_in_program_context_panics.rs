//@ expect: reject
//@ verdict: error
//@ refused-with: a ghost value is dereferenced outside ghost!(...) by a `Deref` the compiler inserts
//@ mechanism: the `Snapshot` twin of ghost_implicit_deref_in_program_context_panics: a deref coercion
//@ mechanism: of a snapshot in program code is a run-time call of `<Snapshot<T> as Deref>::deref`,
//@ mechanism: which panics ("Snapshot deref called at runtime"). Creusot's `Snapshot` deref is a
//@ mechanism: logic function and cannot be called from a program at all.
//@ accept-means: `f` panics on every call while `result == 5` is reported verified.
//@ fixed-by: D-139 — the program-context validator reads the compiler's deref adjustments.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed; natively it panics. Refused under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 5)]
pub fn f() -> i32 {
    let s = snapshot!(5i32);
    let r: &i32 = &s;
    *r
}
