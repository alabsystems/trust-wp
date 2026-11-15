//@ expect: reject
//@ mechanism: the isolating twin of returned_borrow_after_call_final_stale.rs: the same
//@ mechanism: false postcondition on the same returned borrow, with the crediting call
//@ mechanism: removed. It is what says that case is about the CALL's prophecy credit and
//@ mechanism: not about returned borrows in general.
//@ accept-means: a returned borrow's final value could be claimed outright.
//@ WHY THE PROGRAM IS WRONG: `g` returns the borrow, so `^x == ^result` and the caller
//@ WHY THE PROGRAM IS WRONG: chooses it; `^x == 1` is false for any caller that writes
//@ WHY THE PROGRAM IS WRONG: something else through the result.
//@ teeth: rejected today; committed as the control on the attribution, not as a live hole.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn g(x: &mut i32) -> &mut i32 {
    x
}
