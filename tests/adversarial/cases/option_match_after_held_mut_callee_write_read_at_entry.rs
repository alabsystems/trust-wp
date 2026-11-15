//@ expect: reject
//@ mechanism: the `Option`-match spellings of by_value_held_mut_written_by_callee_unseen.rs. A by-value
//@ mechanism: `mut x: Option<u32>` pinned to `None` by its precondition is handed to `put` as
//@ mechanism: `Some(&mut x)`, which writes `Some(5)` through it; the call lane gives no post-call value to a
//@ mechanism: borrow held below the top of an argument. `caller_precondition` then owes `need_none`'s
//@ mechanism: precondition, a `match` on its argument; `caller_return` returns `x.is_none()` under a
//@ mechanism: postcondition that matches the entry `x`. Each match reads a constant the phantom upgrade split
//@ mechanism: from the one `x.is_none()` constrains. A link of the two reads, which D-218 refuses, let the stale
//@ mechanism: entry fact prove both where the host read `x` after the call at its entry value. The call-result
//@ mechanism: spelling is option_match_after_held_mut_callee_write_reads_call_result.rs.
//@ accept-means: a callee's precondition, or a postcondition, is discharged from a parameter's entry value
//@ accept-means: after a callee wrote it through a borrow held in an `Option`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: after `put` `x` is `Some(5)`: `need_none`'s precondition is false at the
//@ WHY THE CONTRACT IS FALSE: call, and `caller_return` returns `false` where its postcondition's
//@ WHY THE CONTRACT IS FALSE: `None` arm (the entry `x`) demands `true`.
//@ fixed-by: n/a — a pin. On this tree each host owes the fail-closed `false` trust-wp injects for the call,
//@ fixed-by: with or without the link, and so does the `o.is_none()` spelling of `need_none`'s precondition;
//@ fixed-by: the case keeps a link from crediting the stale read should that `false` be lifted.
//@ teeth: MEASURED ACCEPTED, exit 0, with the link at the review's head: `caller_precondition verified`,
//@ teeth: `caller_return verified`. On this tree both are unknown with the link (the fail-closed `false`);
//@ teeth: with D-218 `caller_precondition` is unknown (the fail-closed `false`) and `caller_return` is
//@ teeth: `unknown (refutation withheld)`.
//@ also-verified: put, need_none
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
pub fn put(o: Option<&mut Option<u32>>) {
    if let Some(r) = o {
        *r = Some(5);
    }
}

#[requires(match o { Some(_) => false, None => true })]
#[ensures(true)]
pub fn need_none(o: Option<u32>) {}

#[requires(x.is_none())]
pub fn caller_precondition(mut x: Option<u32>) {
    put(Some(&mut x));
    need_none(x);
}

#[requires(x.is_none())]
#[ensures(match x { Some(_) => false, None => result })]
pub fn caller_return(mut x: Option<u32>) -> bool {
    put(Some(&mut x));
    x.is_none()
}
