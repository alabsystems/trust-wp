//@ expect: reject
//@ mechanism: the same call-site prophecy credit the `*_call_then_direct_write_final_stale`
//@ mechanism: cases close, in the spelling where nothing WRITES the referent afterwards
//@ mechanism: because the borrow ESCAPES instead: `f` hands `x` back to its caller. The
//@ mechanism: call binds the callee's `^r` onto the caller's `Final(x)`, and what decides
//@ mechanism: `^x` is then the caller's use of `result` — `^x == ^result` — not the call.
//@ mechanism: The disqualification rule is keyed on a WRITE reaching the referent (a deref
//@ mechanism: store, a `copy_nonoverlapping`, a later call handed the borrow); a return
//@ mechanism: moves the borrow out through a bare assignment to `_0`, which `note_write`
//@ mechanism: deliberately ignores, so the credit survives.
//@ accept-means: a function may promise ANY final value for a `&mut` parameter it gives
//@ accept-means: back to its caller, as long as it routes that value through one contracted
//@ accept-means: call first — the caller's own writes through the returned borrow cannot
//@ accept-means: contradict it.
//@ WHY THE PROGRAM IS WRONG: `f` returns the borrow, so the caller decides `^x`:
//@ WHY THE PROGRAM IS WRONG: `let r = f(&mut a); *r = 7;` leaves `a == 7`, and `^x == 1`
//@ WHY THE PROGRAM IS WRONG: says `a == 1`. `^x == ^result` is the only final-value claim
//@ WHY THE PROGRAM IS WRONG: this body supports.
//@ fixed-by: D-80
//@ teeth: LIVE: ACCEPTED. The isolating twin returned_borrow_no_call_final_stale.rs — same
//@ teeth: contract, same return, no crediting call — is REJECTED on the same binary, so the
//@ teeth: call's credit is what opens this and not the return lane.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32) -> &mut i32 {
    set(x);
    x
}
