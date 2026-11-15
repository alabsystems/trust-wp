//@ expect: reject
//@ mechanism: D-142 reads a switch edge as dead only when EVERY crossing of it proved it not taken.
//@ mechanism: `flag` reaches its switch by two paths: literal `false` when `!c`, literal `true` when
//@ mechanism: `c`. The first path's literal proves the `panic!()` edge dead on that path alone; the
//@ mechanism: second takes it. Reading one crossing's proof as covering the other would credit this
//@ mechanism: body.
//@ accept-means: a proof stated on one path to a switch was read as covering another path to it.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims no execution panics; `hop(true)` sets
//@ WHY THE CONTRACT IS FALSE: `flag` and reaches `panic!()`.
//@ verdict: failed
//@ fn-failed: hop
//@ teeth: VERIFIED — ACCEPTED (`hop verified`) on a build whose recorder kept an edge dead when ANY
//@ teeth: crossing proved it instead of every crossing; the knob was a local patch, reverted.
//@ teeth: With D-169 the walk refutes the arm outright (`hop FAILED` on `!c`), before any cap is read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop(c: bool) -> u32 {
    let mut flag = false;
    if c {
        flag = true;
    }
    if flag {
        panic!()
    }
    0
}
