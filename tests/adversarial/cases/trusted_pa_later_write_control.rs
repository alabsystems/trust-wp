//@ expect: verify
//@ mechanism: isolating twin of `trusted_pa_later_write` — the same write and the same trusted fact, returning the written value, so the postcondition holds without any assumption
//@ teeth: over-refusal control — measured `assumed=1`, exit 2, before the fix; `launder verified ✓`, exit 0, after it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 0i32)]
pub fn launder(mut y: i32) -> i32 {
    y = 0i32;
    #[trusted]
    proof_assert! { y == 0i32 };
    y
}
