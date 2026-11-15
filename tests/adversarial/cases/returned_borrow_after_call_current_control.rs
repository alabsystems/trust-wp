//@ expect: verify
//@ xfail: trust-wp has no encoding for the CURRENT pointee of a returned `&mut` parameter:
//@ xfail: it binds `result` to the parameter's own final-value carrier, so `*result` and
//@ xfail: `^x` are one symbol and this clause IS the clause of the RED twin beside it. The
//@ xfail: accept it used to get came from the same false credit; nothing separable was
//@ xfail: lost. returned_borrow_no_call_current_control.rs is the proof — the same claim
//@ xfail: with no call to credit anything is unprovable on the binary that accepted this.
//@ mechanism: control for returned_borrow_after_call_final_stale.rs: the CURRENT value of
//@ mechanism: the returned borrow is exactly what the call does establish, because the
//@ mechanism: reborrow handed to `set` expires at the return and its final flows into
//@ mechanism: `*x`. It is xfail rather than verifying because trust-wp cannot state it
//@ mechanism: apart from `^x`; the pair that isolates the fix is instead
//@ mechanism: call_final_credit_no_later_write_control.rs, which makes the SAME `^x == 1`
//@ mechanism: claim over the SAME call and keeps verifying because its borrow does not
//@ mechanism: escape.
//@ teeth: control - xfail, and the separable current-value claim needs a result encoding
//@ teeth: this driver does not have.
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
#[ensures(*result == 1i32)]
pub fn f(x: &mut i32) -> &mut i32 {
    set(x);
    x
}
