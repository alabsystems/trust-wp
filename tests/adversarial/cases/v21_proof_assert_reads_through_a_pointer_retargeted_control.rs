//@ expect: verify
//@ mechanism: the control of D-187: a read through a pointer whose re-targeting PRECEDES the store
//@ mechanism: keeps the store's recorded value: re-target then store (retarget_then_store), a store
//@ mechanism: and a branch that leaves the pointer alone (store_without_retarget), a second store
//@ mechanism: after the re-target (retarget_store_again), and a re-target in a loop followed by the
//@ mechanism: store (retarget_in_loop_then_store).
//@ fixed-by: n/a (over-refusal guard for D-187)
//@ teeth: MEASURED: every assertion verifies on 5f9337a5 (D-186) and with D-187.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn retarget_then_store<'a>(a: &'a mut i32, b: &'a mut i32, c: bool) {
    let mut p: &mut i32 = a;
    if c {
        p = b;
    }
    *p = 0i32;
    proof_assert!(*p == 0i32);
}

pub fn store_without_retarget(a: &mut i32, c: bool) {
    let p: &mut i32 = a;
    *p = 0i32;
    if c {
        let _k = 1u8;
    }
    proof_assert!(*p == 0i32);
}

pub fn retarget_store_again<'a>(a: &'a mut i32, b: &'a mut i32) {
    let mut p: &mut i32 = a;
    *p = 1i32;
    p = b;
    *p = 0i32;
    proof_assert!(*p == 0i32);
}

pub fn retarget_in_loop_then_store<'a>(a: &'a mut i32, b: &'a mut i32, n: u32) {
    let mut p: &mut i32 = a;
    let mut i = 0u32;
    while i < n {
        p = &mut *b;
        i += 1;
    }
    *p = 0i32;
    proof_assert!(*p == 0i32);
}
