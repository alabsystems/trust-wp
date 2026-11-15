//@ expect: verify
//@ xfail: a `let (mut $n, _) = (..)` tuple destructure's assertion is `unknown (proof_assert slice
//@ xfail: lacks exact strict proof authority)` on the D-239 build, the tuple lane's completeness gap.
//@ xfail-verdict: unknown
//@ mechanism: control for r31_macro_mut_ident_binding_hygiene.rs hm8 (D-239): the macro's tuple
//@ mechanism: pattern binds the caller's `x` to 0, and the assertion says so.
//@ accept-means: n/a (control) - the assertion holds.
//@ teeth: MEASURED: FAILED (a false refutation) on 62994450 (D-238); `unknown` with D-239.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! bind_tuple_mut {
    ($n:ident) => {
        let (mut $n, _) = (0i32, 1i32);
        $n += 0;
    };
}

#[requires(x@ == 5)]
pub fn hc8(x: i32) {
    bind_tuple_mut!(x);
    proof_assert!(x@ == 0);
}
