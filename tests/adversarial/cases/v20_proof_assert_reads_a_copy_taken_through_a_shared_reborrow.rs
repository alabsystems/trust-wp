//@ expect: reject
//@ mechanism: a copy taken through a shared reborrow of a `&mut` parameter's pointee (`let r = &*x;
//@ mechanism: let v = *r;`) before a store `*x = 5` is read by a `proof_assert!` as the stored value.
//@ mechanism: D-185 counted a local shared reference as frozen memory, so the walk's current-value
//@ mechanism: binding `*r -> 5` stayed a fact; `r` resolves to `x`, and the fact became `*x == 5`
//@ mechanism: about the entry symbol the copy `v` is bound to (r7b: `v == 5`; r7: `v == w` for a
//@ mechanism: copy `w` after the store; r7e: `v == *x`).
//@ accept-means: a copy taken through a reborrow before a write is read at the written value.
//@ WHY THE CONTRACT IS FALSE: under `requires(*x == 0)` the copy `v` is 0 and `*x` (and `w`) is 5.
//@ fixed-by: D-186 (only a shared reference parameter is frozen memory; a local borrow of a
//@ fixed-by: parameter's memory is written memory, whose current-value bindings are no facts)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 4c67cea8 (D-185) r7, r7b and r7e were VERIFIED with their proof_asserts and the
//@ teeth: crate ACCEPTED; with D-186 each is unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(*x == 0i32)]
pub fn r7(x: &mut i32) {
    let r: &i32 = &*x;
    let v = *r;
    *x = 5i32;
    let w = *x;
    proof_assert!(w == v);
}

#[requires(*x == 0i32)]
pub fn r7b(x: &mut i32) {
    let r: &i32 = &*x;
    let v = *r;
    *x = 5i32;
    proof_assert!(v == 5i32);
}

#[requires(*x == 0i32)]
pub fn r7e(x: &mut i32) {
    let r: &i32 = &*x;
    let v = *r;
    *x = 5i32;
    proof_assert!(v == *x);
}
