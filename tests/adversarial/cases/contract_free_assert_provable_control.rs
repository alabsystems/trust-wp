//@ expect: verify
//@ mechanism: control for the contract-free discovery pass — a contract-free fn whose `assert!`
//@ mechanism: is provable from the body itself. The switch lane charges the failing arm and
//@ mechanism: discharges it, and `cap_clause_free_verdict` reads that charged edge as dead (D-142).
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn ok() {
    let a = 1u32;
    assert!(a == 1);
}
