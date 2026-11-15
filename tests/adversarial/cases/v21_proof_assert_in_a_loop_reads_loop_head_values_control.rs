//@ expect: verify
//@ mechanism: the control of D-187: an assertion in a loop body that holds at EVERY iteration is
//@ mechanism: still proved once loop-carried locals are read at the loop head: a local the body
//@ mechanism: sets before the read (local_set_before_read), the loop condition (condition_holds_in_body),
//@ mechanism: an invariant over a local the body writes after the read (invariant_constrains), a
//@ mechanism: local the loop never writes (unwritten_in_loop), an assertion after the loop
//@ mechanism: (after_loop), an invariant over the counter (inv_counter), and a write between the
//@ mechanism: loop head and the assertion beside an invariant about the head (inv_then_write, the
//@ mechanism: example contract-syntax.md gives).
//@ fixed-by: n/a (over-refusal guard for D-187)
//@ teeth: MEASURED: every function and assertion verifies with D-187; on 5f9337a5 (D-186)
//@ teeth: inv_then_write's first assertion was refused as vacuous (`y == 5` from the walk beside
//@ teeth: the head invariant `y == 0` over one symbol) and the rest verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn local_set_before_read(n: u32) {
    let mut i = 0u32;
    while i < n {
        let k = 3i32;
        proof_assert!(k == 3i32);
        i += 1;
    }
}

pub fn condition_holds_in_body(n: u32) {
    let mut i = 0u32;
    while i < n {
        proof_assert!(i < n);
        i += 1;
    }
}

pub fn invariant_constrains(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    #[invariant(y == 0i32)]
    while i < n {
        proof_assert!(y == 0i32);
        y = 0i32;
        i += 1;
    }
}

pub fn unwritten_in_loop(n: u32) {
    let y = 4i32;
    let mut i = 0u32;
    while i < n {
        proof_assert!(y == 4i32);
        i += 1;
    }
}

pub fn after_loop(n: u32) {
    let mut i = 0u32;
    while i < n {
        i += 1;
    }
    let y = 2i32;
    proof_assert!(y == 2i32);
}

pub fn inv_counter(n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        proof_assert!(i < n);
        i += 1;
    }
}

pub fn inv_then_write(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    #[invariant(y == 0i32)]
    while i < n {
        proof_assert!(y == 0i32 && i < n);
        y = 5i32;
        proof_assert!(y == 5i32);
        y = 0i32;
        i += 1;
    }
}
