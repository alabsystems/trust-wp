//@ expect: verify
//@ mechanism: constructor-equality payload facts — control (true equality over the same shapes)
//@ fixed-by: cfff9b4 (s25 vacuous whole-value equality)
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn res_lit_true() {
    let r: Result<i32, i32> = Err(3i32);
    proof_assert!(r == Err(3i32));
}
