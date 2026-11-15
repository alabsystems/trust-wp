//@ expect: verify
//@ mechanism: the TRUE twin of std_spec_vecdeque_with_capacity_overflow_panics, identical but for
//@ mechanism: the element type: a zero-sized element occupies no bytes, so `with_capacity` never
//@ mechanism: panics whatever the capacity, and the requirement the call site writes is
//@ mechanism: `capacity@ * 0 <= isize::MAX@`. It pins that the size is read from THIS call's type:
//@ mechanism: a requirement that ignored the element type would refuse this call too.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `g verified ✓`, exit 0, with and without the twin's requirement.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::collections::VecDeque;

#[requires(n@ >= 1152921504606846976)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    let d: VecDeque<()> = VecDeque::with_capacity(n);
    d.len()
}
