//@ expect: reject
//@ mechanism: the grant side of closure_call_reassigned_param_capture_reads_entry_value: a `move`
//@ mechanism: closure's `ensures(result@ == x@)` over a capture of a parameter reassigned before the
//@ mechanism: closure is built. Read off the capture's value (`5`), the call binds no name, and the
//@ mechanism: credit states `result == x` over the caller's parameter symbol, its ENTRY value `0`, so
//@ mechanism: the caller's false `result@ == 0` follows.
//@ accept-means: a closure's postcondition about a capture is credited to the caller's entry value.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: caller(0) returns 5, the captured value.
//@ fixed-by: fix(closure-call): a call binds each capture by the names the closure's own contract lane reads it by
//@ teeth: `caller verified` without the fix named in `fixed-by:` (the closure itself is refuted in
//@ teeth: its own lane, so only the per-function gate sees the false credit); with the capture
//@ teeth: bound, the credit states the post-call value of the constant the capture holds, which the
//@ teeth: final-collapse guard refuses (D-14).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
#[ensures(result@ == 0)]
pub fn caller(mut x: i32) -> i32 {
    x = 5;
    let c = #[ensures(result@ == x@)]
    move || -> i32 { x };
    c()
}
