//@ expect: verify
//@ mechanism: control for D-142's path count — the `assert!` switch is reached by two paths (the
//@ mechanism: arms of `if x > 3`), the walk crosses it on both, and on each the failing arm is
//@ mechanism: charged and discharged. An edge is dead only when the walk crossed its switch on
//@ mechanism: every path from the entry; this pins that two walked paths count as two.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop(x: u32) -> u32 {
    let y = if x > 3 { 1 } else { 2 };
    assert!(y > 0);
    y
}
