//@ expect: verify
//@ xfail: the TRUE twin of closure_call_projected_capture_precondition_read_at_entry: the closure
//@ xfail: requires the value its projected capture holds (5), and the call owes it over the
//@ xfail: caller's parameter symbol, its ENTRY value 0, so a TRUE call is refuted. Retire this
//@ xfail: directive when a projected capture is bound by the path the closure's own lane reads.
//@ xfail-verdict: failed
//@ mechanism: control for closure_call_projected_capture_precondition_read_at_entry.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p.0@ == 0)]
pub fn caller(mut p: (i32, i32)) -> i32 {
    p.0 = 5;
    let c = #[requires(p.0@ == 5)]
    move || -> i32 { p.0 };
    c()
}
