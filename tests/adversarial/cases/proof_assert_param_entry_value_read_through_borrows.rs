//@ expect: reject
//@ mechanism: a by-value parameter written before a shared borrow of it, or of a field of it, and
//@ mechanism: the borrow read by the assertion or handed to a callee whose postcondition reads it,
//@ mechanism: beside a copy of the parameter's entry value. The walks name a borrowed place by its
//@ mechanism: owner's name, a reference identity: once the lane names a re-bound parameter's entry
//@ mechanism: value apart from its value at the assertion (D-241), that name inside a recorded value
//@ mechanism: is the entry value, so a borrow taken after the write would read the value before it,
//@ mechanism: and the copy and the borrow would be read by one symbol. On D-240 the copy followed the
//@ mechanism: write instead (`let y = x; x = 5;` read `y` as 5), and a field write left the parameter
//@ mechanism: at its own name, the entry value its `#[requires]` constrains.
//@ accept-means: an assertion about a value read through a shared borrow of a written parameter, or
//@ accept-means: about a copy of the parameter taken before the write, is credited from the value the
//@ accept-means: parameter had on the other side of the write.
//@ WHY THE CONTRACT IS FALSE: `shared_ref_after_rebind(0)` reads 5 through `r`;
//@ WHY THE CONTRACT IS FALSE: `shared_field_ref_after_write((0, 0))` and `shared_whole_ref_after_write((0, 0))`
//@ WHY THE CONTRACT IS FALSE: read 5; `copy_then_shared_borrow(0)` has `y == 0`;
//@ WHY THE CONTRACT IS FALSE: `copy_then_read_call(0)` has `r == 5` and `y == 0`.
//@ fixed-by: D-241: a shared borrow of a written by-value parameter is read at the parameter's binding
//@ fixed-by: when it is taken, and the parameter's entry value has a symbol of its own.
//@ teeth: MEASURED on D-240: `shared_field_ref_after_write`, `shared_whole_ref_after_write`,
//@ teeth: `copy_then_shared_borrow` and `copy_then_read_call` verified, `shared_ref_after_rebind`
//@ teeth: FAILED; with D-241 each is rejected. Without the shared-borrow reading of D-241 (the entry
//@ teeth: symbol alone), `shared_ref_after_rebind` and `copy_then_read_call` verified.
//@ also-verified: read
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == *a)]
pub fn read(a: &u32) -> u32 {
    *a
}

#[requires(x@ == 0)]
pub fn shared_ref_after_rebind(mut x: u32) {
    x = 5;
    let r = &x;
    proof_assert!((*r)@ == 0);
}

#[requires(p.0@ == 0)]
pub fn shared_field_ref_after_write(mut p: (u32, u32)) {
    p.0 = 5;
    let r = &p.0;
    proof_assert!((*r)@ == 0);
}

#[requires(p.0@ == 0)]
pub fn shared_whole_ref_after_write(mut p: (u32, u32)) {
    p.0 = 5;
    let r = &p;
    proof_assert!(r.0@ == 0);
}

pub fn copy_then_shared_borrow(mut x: u32) {
    let y = x;
    x = 5;
    let r = &x;
    proof_assert!(y@ == 5 && (*r)@ == 5);
}

pub fn copy_then_read_call(mut x: u32) {
    let y = x;
    x = 5;
    let r = read(&x);
    proof_assert!(r == y);
}
