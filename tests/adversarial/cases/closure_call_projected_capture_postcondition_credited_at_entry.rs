//@ expect: reject
//@ mechanism: the grant side of closure_call_projected_capture_precondition_read_at_entry. The
//@ mechanism: closure's `ensures(result@ == p.0@)` reads a projected capture the call binds by no
//@ mechanism: name, so the call's credit states `result == p.0` over the caller's parameter symbol,
//@ mechanism: its ENTRY value 0, and the caller's false `result@ == 0` follows.
//@ accept-means: a closure's postcondition about a projected capture is credited to the caller's
//@ accept-means: entry value.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: caller((0, 0)) returns 5, the value p.0
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: holds when the closure is built.
//@ teeth: UNVERIFIED — `caller verified` with and without the capture-binding fix; the defect is
//@ teeth: live. The closure itself is refuted in its own lane (an over-refusal of a TRUE clause), so
//@ teeth: the crate exits 1 and only the per-function gate sees the caller's false credit.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p.0@ == 0)]
#[ensures(result@ == 0)]
pub fn caller(mut p: (i32, i32)) -> i32 {
    p.0 = 5;
    let c = #[ensures(result@ == p.0@)]
    move || -> i32 { p.0 };
    c()
}
