//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_instant_checked_add_none_unwrapped, identical but for the
//@ mechanism: duration: adding zero never leaves the clock's range, and the spec still says so.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::{Duration, Instant};

#[ensures(true)]
pub fn f() -> bool {
    let t = Instant::now().checked_add(Duration::from_secs(0)).unwrap();
    t == t
}
