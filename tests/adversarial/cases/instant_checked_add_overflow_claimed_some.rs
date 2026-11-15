//@ expect: reject
//@ mechanism: the false half of the isolating pair for D-116. The builtin std spec of
//@ mechanism: `Instant::checked_add` said the call never returns `None`, on the ground that the
//@ mechanism: abstract Instant view is an unbounded Int. The view is unbounded; the platform clock
//@ mechanism: is not: adding `Duration::MAX` overflows the timestamp's seconds and `checked_add`
//@ mechanism: returns `None`. The spec granted `is_some()` of a call that returns `None`.
//@ accept-means: `Instant::now().checked_add(Duration::MAX).is_some()` evaluates to `false` when run
//@ accept-means: (measured on aarch64-apple-darwin); an accept claims it returns `true`.
//@ fixed-by: D-116
//@ teeth: ACCEPTED (`overflow_is_some verified`) on the build before D-116.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::{Duration, Instant};

#[ensures(result)]
pub fn overflow_is_some() -> bool {
    let i = Instant::now();
    i.checked_add(Duration::MAX).is_some()
}
