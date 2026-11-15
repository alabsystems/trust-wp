//@ expect: reject
//@ verdict: error
//@ refused-with: as std::ops::Add>` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: trust-wp-std's `Int` is `Int(pub i128)` at run time and its `Add` is `i128` addition,
//@ mechanism: which overflows past `i128::MAX`. A generic function of the crate's own, bounded by `Add`,
//@ mechanism: reads `a + b` as a call with no precondition; given `Int`, its body runs `<Int as Add>::add`
//@ mechanism: on the host `i128`. The caller is credited, though the call panics: nothing at the call
//@ mechanism: site asks what the instance's `add` does at run time, where the logic reading has no
//@ mechanism: overflow to owe.
//@ accept-means: a program body that hands `Int`s to an `Add`-bounded function is credited `verified`,
//@ accept-means: though the call panics.
//@ fixed-by: D-193: a call whose instantiated bounds ask `Int` for an arithmetic trait is refused in
//@ fixed-by: code that runs, as a direct `Int` operation is.
//@ WHY THE CONTRACT IS FALSE: `caller` panics on every call ("attempt to add with overflow").
//@ teeth: at the campaign base 6e6bf5f3, `caller` verified (`add` FAILED on its generic `a + b`).
//@ teeth: Natively, against the campaign's debug trust-wp-std, `caller` panics in `<Int as Add>::add`.
//@ teeth: Refused at wp-s150; logic_int_exact_operations_in_program_context_control verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::ops::Add;

#[ensures(true)]
pub fn add<T: Add<Output = T>>(a: T, b: T) -> T {
    a + b
}

#[ensures(true)]
pub fn caller() -> bool {
    let _c = add(Int(i128::MAX), Int(1));
    true
}
