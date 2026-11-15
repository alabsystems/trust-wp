//@ expect: reject
//@ mechanism: a `proof_assert!` reads through a `&mut` pointer that is RE-TARGETED after a store
//@ mechanism: through it: `let mut p = a; *p = 0; if c { p = b; } proof_assert!(*p == 0)` (rbs),
//@ mechanism: a lifetime-annotated local (rp1), a by-`mut` reference parameter `x = y` (rp4), the
//@ mechanism: same under `#[requires(*b == 9)]` (rb_req), `p = &mut z` of a local (rb_local), the
//@ mechanism: re-target in a match arm (rb_match), under a nested `if` (rb_nested), as a reborrow
//@ mechanism: `p = &mut *b` (rb_reborrow), and in a loop body after the assertion (rb_inloop).
//@ mechanism: D-186 took `*p = 0` as the one whole-pointee store reaching the read, because
//@ mechanism: re-binding `p` itself was no write site of the pointee, and read the recorded 0
//@ mechanism: although on the re-targeted path `p` points at `*b`, which the store never wrote.
//@ accept-means: a read through a pointer is credited with a value stored through ANOTHER value of
//@ accept-means: that pointer.
//@ WHY THE CONTRACT IS FALSE: with `c` true (k = 3 for rb_match, c = d = true for rb_nested, n = 2
//@ WHY THE CONTRACT IS FALSE: for rb_inloop) and `*b` = 9 (z = 9 for rb_local), `*p` at the
//@ WHY THE CONTRACT IS FALSE: assertion is 9, never 0.
//@ fixed-by: D-187 (a read through `p` takes a store's recorded value only when no definition of
//@ fixed-by: `p` itself lies on a path from that store to the read)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 5f9337a5 (D-186) every proof_assert here was VERIFIED, rb_req's and rb_inloop's
//@ teeth: functions too, and the crate was ACCEPTED; with D-187 each is refused as a stale read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn rbs<'a>(a: &'a mut i32, b: &'a mut i32, c: bool) {
    let mut p: &mut i32 = a;
    *p = 0i32;
    if c {
        p = b;
    }
    proof_assert!(*p == 0i32);
}

pub fn rp1<'a>(a: &'a mut i32, b: &'a mut i32, c: bool) {
    let mut p: &'a mut i32 = a;
    *p = 0i32;
    if c {
        p = b;
    }
    proof_assert!(*p == 0i32);
}

pub fn rp4<'a>(mut x: &'a mut i32, y: &'a mut i32, c: bool) {
    *x = 0i32;
    if c {
        x = y;
    }
    proof_assert!(*x == 0i32);
}

#[requires(*b == 9i32)]
pub fn rb_req<'a>(a: &'a mut i32, b: &'a mut i32, c: bool) {
    let mut p: &mut i32 = a;
    *p = 0i32;
    if c {
        p = b;
    }
    proof_assert!(*p == 0i32);
}

pub fn rb_local(a: &mut i32, c: bool) {
    let mut z = 9i32;
    let mut p: &mut i32 = a;
    *p = 0i32;
    if c {
        p = &mut z;
    }
    proof_assert!(*p == 0i32);
}

pub fn rb_match<'a>(a: &'a mut i32, b: &'a mut i32, k: u8) {
    let mut p: &mut i32 = a;
    *p = 0i32;
    match k {
        3u8 => {
            p = b;
        }
        _ => {}
    }
    proof_assert!(*p == 0i32);
}

pub fn rb_nested<'a>(a: &'a mut i32, b: &'a mut i32, c: bool, d: bool) {
    let mut p: &mut i32 = a;
    *p = 0i32;
    if c {
        if d {
            p = b;
        }
    }
    proof_assert!(*p == 0i32);
}

pub fn rb_reborrow<'a>(a: &'a mut i32, b: &'a mut i32, c: bool) {
    let mut p: &mut i32 = &mut *a;
    *p = 0i32;
    if c {
        p = &mut *b;
    }
    proof_assert!(*p == 0i32);
}

pub fn rb_inloop<'a>(a: &'a mut i32, b: &'a mut i32, n: u32) {
    let mut p: &mut i32 = a;
    let mut i = 0u32;
    *p = 0i32;
    while i < n {
        proof_assert!(*p == 0i32);
        p = &mut *b;
        i += 1;
    }
}
