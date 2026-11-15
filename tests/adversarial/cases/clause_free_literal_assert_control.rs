//@ expect: verify
//@ mechanism: control for D-142 — a clause-free body whose panic arms a literal discriminant never
//@ mechanism: selects: `assert!(!false)` and `assert!(true)` lower to a switch on a temporary
//@ mechanism: assigned only from a constant, so the failing arm is dead by the value itself, with
//@ mechanism: no obligation to state (the should_succeed rows lang/unary_op and match_int); and a
//@ mechanism: switch on `c`, a local assigned only the literal `true`, never takes its `else` edge.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop() -> u32 {
    assert!(!false);
    assert!(true);
    let c = true;
    if c { 1 } else { unreachable!() }
}
