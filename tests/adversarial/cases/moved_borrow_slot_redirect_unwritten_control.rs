//@ expect: verify
//@ xfail: over-refusal, and the named price of D-79. The redirect stores `b`'s borrow through a
//@ xfail: deref into a slot no lane models, so the borrow is charged at the escape instead of at
//@ xfail: a later write through the slot. Nothing writes through the slot here, so `^b == *b` is
//@ xfail: TRUE. Retire this when the alias record carries WHICH borrow the slot currently holds,
//@ xfail: which lets the havoc wait for a write that could actually reach the redirected
//@ xfail: referent.
//@ mechanism: The redirect of moved_borrow_slot_redirect_other_root_write_lost with the write
//@ mechanism: that follows it deleted. `b`'s borrow reaches the slot and dies there unwritten,
//@ mechanism: so its pointee keeps its entry value — this case exists so the price of charging
//@ mechanism: the escape at the store is recorded as a cost rather than found later as a
//@ mechanism: mystery.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^b == *b)]
pub fn f(a: &mut i32, b: &mut i32) {
    let mut p = a;
    let s = &mut p;
    *s = b;
}
