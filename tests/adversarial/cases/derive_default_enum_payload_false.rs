//@ expect: reject
//@ mechanism: isolating twin of `derive_default_enum_payload_control` — the same derived default, read by a caller whose claim contradicts the payload's default
//@ accept-means: a caller proved the default variant's first field is 1 when the derive builds it as 0
//@ also-verified: <E as std::default::Default>::default
//@ teeth: none today — `first` is `unknown` (the caller-side read is the gap its control records); the case pins that it is never credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use creusot_std::prelude::Default;

#[derive(Default)]
pub enum E {
    #[default]
    A(i32, i32),
    B,
}

// WRONG: E::default() is A(0, 0), so first() returns 0.
#[ensures(result == 1i32)]
pub fn first() -> i32 {
    match E::default() {
        E::A(x, _) => x,
        E::B => 1i32,
    }
}
