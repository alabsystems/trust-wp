//@ expect: verify
//@ xfail: the price of the every-visit rule. The switch on `y` is visited twice: on the `c` path `y` is the literal `false`, its arm's walk meets the literal-taken `if b` and the gate charges the arm with `!false`; on the `!c` path `b` is `false`, the inner arm is charged as dead but the outer arm is not. One visit left the outer arm uncharged, so the cap walks into it and meets the inner panic, which the `c` visit left uncharged. The body never panics.
//@ mechanism: the clause-free cap (`unchecked_panic_sites`) skips a switch edge only when EVERY walk visit of the switch stated the edge unreachable as a goal of the verified VC (`ProvedDeadEdges`, D-142: recorded by the lane that pushed the goal, only where `primary_arithmetic_is_exact`).
//@ mechanism: control that pins the conservative side of that rule: crediting an edge because ONE visit charged it would also hide any unchecked site inside the arm on the path whose visit charged nothing.
//@ accept-means: n/a (control)
//@ teeth: verifies when an edge is credited on any visit (measured with a local knob on the recorder D-142 replaced); capped here.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool, x: bool) {
    let b;
    let y;
    if c {
        b = true;
        y = false;
    } else {
        b = false;
        y = x;
    }
    if y {
        if b {
            panic!()
        }
    }
}
