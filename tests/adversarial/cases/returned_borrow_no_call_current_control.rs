//@ expect: verify
//@ xfail: the current pointee of a returned `&mut` parameter is not expressible: `result`
//@ xfail: binds to the parameter's final-value carrier, so `*result` reads as `^x`, which
//@ xfail: the caller decides and nothing here constrains.
//@ mechanism: the floor under returned_borrow_after_call_current_control.rs. Nothing is
//@ mechanism: written and nothing is called, so `*result` is the entry pointee and the
//@ mechanism: claim is TRUE by inspection; it is refused anyway. That is what says the
//@ mechanism: accept its with-a-call sibling used to get was the stale prophecy credit
//@ mechanism: standing in for a current value, and not a capability a credit rule can cost.
//@ teeth: control - xfail, and xfail on the binary that still ACCEPTED the RED twins, so
//@ teeth: it is a pre-existing encoding gap and not a price paid for closing them.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x == 0i32)]
#[ensures(*result == 0i32)]
pub fn g(x: &mut i32) -> &mut i32 {
    x
}
