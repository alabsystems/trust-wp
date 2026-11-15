//@ expect: reject
//@ mechanism: the call-result spelling of option_match_after_held_mut_callee_write_read_at_entry.rs: the
//@ mechanism: local handed to `put` as `Some(&mut y)` holds a call result (`let mut y = mk()`), so the
//@ mechanism: stale name the host reads after the call is the call result itself, which `mk`'s
//@ mechanism: postcondition pins to `None`, and `need_none`'s precondition matches it. The link of the
//@ mechanism: split reads that D-218 refuses declared a call result as it did a parameter, so
//@ mechanism: a link restricted to call results, whose value never changes, would still let the stale
//@ mechanism: read reach the arms.
//@ accept-means: a callee's precondition is discharged from a call result's value after a callee wrote the
//@ accept-means: local holding it through a borrow held in an `Option`.
//@ WHY THE CONTRACT IS FALSE: after `put` `y` is `Some(5)`, so `need_none`'s precondition is false.
//@ fixed-by: n/a — a pin, as option_match_after_held_mut_callee_write_read_at_entry.rs is: on this tree
//@ fixed-by: `caller_local` owes the fail-closed `false` trust-wp injects for the call, with or without the link.
//@ teeth: MEASURED with the link at the review's head: `caller_local verified`; `mk`'s own credit is
//@ teeth: `verified` or `unknown (proof-trusted)` depending on load. On this tree `caller_local` is unknown
//@ teeth: (the fail-closed `false`) with the link and with D-218.
//@ also-verified: put, need_none, mk
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

#[ensures(result.is_none())]
pub fn mk() -> Option<u32> {
    None
}

pub fn caller_local() {
    let mut y = mk();
    put(Some(&mut y));
    need_none(y);
}
