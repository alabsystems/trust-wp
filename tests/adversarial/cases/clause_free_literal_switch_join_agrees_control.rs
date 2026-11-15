//@ expect: verify
//@ mechanism: control for clause_free_literal_switch_join_differs, which differs in one literal:
//@ mechanism: here `flag` is the literal `false` on both paths to its switch, the walk crosses the
//@ mechanism: switch on each of them, and each crossing proves the `panic!()` edge not taken, so
//@ mechanism: `cap_clause_free_verdict` reads it as dead (D-142).
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop(c: bool) -> u32 {
    let mut flag = false;
    if c {
        flag = false;
    }
    if flag {
        panic!()
    }
    0
}
