//@ expect: reject
//@ mechanism: a `proof_assert!` in a `ghost!` block after the body wrote a by-value parameter, reading
//@ mechanism: the parameter, a copy of it, or a callee's result over it. The lane joins the ghost block's
//@ mechanism: own walk (and its closures' effects) to the main walk's map; those read the parameter's
//@ mechanism: name as its value at the block, the current one, where the main walk's values read it as
//@ mechanism: the entry value. Named apart (D-241) without that difference, a ghost copy of the
//@ mechanism: parameter would be read at its entry value and its `#[requires]`; on D-240 a copy taken
//@ mechanism: before the write followed the write, and a field write was read at the entry value.
//@ accept-means: an assertion in a ghost block about a by-value parameter the body wrote, or about a
//@ accept-means: copy of it, is credited from the value it had on the other side of the write.
//@ WHY THE CONTRACT IS FALSE: `ghost_copy_after_rebind(0)` and `ghost_reads_call_after_rebind(0)` read 5;
//@ WHY THE CONTRACT IS FALSE: `copy_then_ghost(0)` and `ghost_copy_of_copy(0)` have `y == 0`;
//@ WHY THE CONTRACT IS FALSE: `ghost_field_after_write(P { a: 3, b: 0 })` has `p.a == 7`.
//@ fixed-by: D-241: the ghost block's values are read in the main walk's terms before the
//@ fixed-by: parameter's entry value is named apart.
//@ teeth: MEASURED on D-240: `copy_then_ghost`, `ghost_field_after_write` and `ghost_copy_of_copy`
//@ teeth: verified, the other two FAILED. With the entry symbol but the ghost values left in their
//@ teeth: own terms, `ghost_copy_after_rebind` and `ghost_reads_call_after_rebind` verified.
//@ also-verified: read
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: i32,
    pub b: i32,
}

#[ensures(result == *a)]
pub fn read(a: &u32) -> u32 {
    *a
}

#[requires(x@ == 0)]
pub fn ghost_copy_after_rebind(mut x: u32) {
    x = 5;
    ghost! {
        let y = x;
        proof_assert!(y@ == 0);
    };
}

pub fn copy_then_ghost(mut x: u32) {
    let y = x;
    x = 5;
    ghost! {
        proof_assert!(y@ == 5);
    };
}

#[requires(x@ == 0)]
pub fn ghost_reads_call_after_rebind(mut x: u32) {
    x = 5;
    ghost! {
        let r = read(&x);
        proof_assert!(r@ == 0);
    };
}

#[requires(p.a@ == 3)]
pub fn ghost_field_after_write(mut p: P) {
    p.a = 7;
    ghost! {
        proof_assert!(p.a@ == 3);
    };
    let _ = p;
}

#[requires(x@ == 0)]
pub fn ghost_copy_of_copy(mut x: u32) {
    let y = x;
    x = 5;
    ghost! {
        let z = y;
        proof_assert!(z@ == 5);
    };
    let _ = x;
}
