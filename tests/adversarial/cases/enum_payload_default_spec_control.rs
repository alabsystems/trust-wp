//@ expect: verify
//@ mechanism: isolating twin of `enum_payload_default_spec_false` — the same field-level payload claim over a body that keeps it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum E {
    A(i32, i32),
    B,
}

impl Default for E {
    #[ensures(match result { E::A(x0, x1) => x0 == 0i32 && x1 == 0i32, _ => false })]
    fn default() -> Self {
        E::A(0i32, 0i32)
    }
}
