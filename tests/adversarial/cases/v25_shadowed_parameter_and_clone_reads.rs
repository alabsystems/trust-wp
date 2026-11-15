//@ expect: reject
//@ mechanism: more shapes of one source name bound to several locals (D-237). pa2: `let y = x;`
//@ mechanism: copies the PARAMETER x, then `let x = 0;` shadows it; y's value is the name `x`,
//@ mechanism: which the assertion's substitution read as the new `x`, so `y == x` held of a
//@ mechanism: parameter the precondition keeps positive. pa6: a clone of the old `r` and a clone
//@ mechanism: of the new one were both stated as `rK == r`, one name for two receivers. cp3: a ghost
//@ mechanism: snapshot of the parameter `h`, compared with the `h` that shadows it, read both as the
//@ mechanism: parameter. cp2: a closure's body reads its capture by the capture's name, which must
//@ mechanism: name the binding captured, not the parameter of that name. The rest
//@ mechanism: never verified and keep the other shapes in the corpus: an assertion after an inner
//@ mechanism: block's or a branch's or a loop body's shadowing `let` (sb1, sb2, sb4), one inside
//@ mechanism: the block (sb5), a copy before the shadow (sb3), a parameter read after its shadow
//@ mechanism: (pa1), a capture of the shadowed binding (pa3), an invariant over a name a later
//@ mechanism: `let` shadows (pa4), ghost writes to a shadowed or shadowing ghost (pa8, pa9, pa10).
//@ accept-means: a value or fact about one binding is read as one about another of its name.
//@ WHY THE CONTRACT IS FALSE: pa1: x is 0. pa2: y is the parameter (positive), x is 0. pa3: v is 1,
//@ WHY THE CONTRACT IS FALSE: h is 2. pa4: i is 10, n is 3. pa6: r3 holds 2, r2 holds 1. pa7: b is 1,
//@ WHY THE CONTRACT IS FALSE: c is 2. pa8: the visible g holds 2. pa9: the outer g holds 0. pa10: the
//@ WHY THE CONTRACT IS FALSE: visible g holds 4. cp2: v is 2. cp3: g holds 1, h is 2. sb1, sb2, sb4: the visible x is 1. sb3: x is 2,
//@ WHY THE CONTRACT IS FALSE: y is 1. sb5: the inner x is 2.
//@ fixed-by: D-237
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): before D-237 the assertions of
//@ teeth: pa2, pa6 and cp3 VERIFIED (and pa2's and cp3's functions with them); with D-237 every
//@ teeth: assertion FAILED. cp2 FAILED on both; naming the binding without naming the capture apart
//@ teeth: verified it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use ::std::rc::Rc;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
pub fn pa1(x: i32) {
    let x = 0i32;
    proof_assert!(x@ > 0);
}

#[requires(x@ > 0 && x@ < 100)]
pub fn pa2(x: i32) {
    let y = x;
    let x = 0i32;
    proof_assert!(y == x);
}

pub fn pa3() {
    let h = 1i32;
    let cl = || h;
    let h = 2i32;
    let v = cl();
    proof_assert!(v == h);
}

pub fn pa4() {
    let mut i = 0i32;
    let n = 10i32;
    #[invariant(i@ <= n@)]
    while i < n {
        i += 1;
    }
    let n = 3i32;
    proof_assert!(i@ <= n@);
}

pub fn pa6() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    let r = Rc::new(2i32);
    let r3 = r.clone();
    proof_assert!(r3 == r2);
}

pub fn pa7() {
    let a = 1i32;
    let b = a;
    let a = 2i32;
    let c = a;
    proof_assert!(b == c);
}

pub fn pa8() {
    let mut g = ghost! {0i32};
    let _ = ghost! {
        *g = 1i32;
    };
    let g = ghost! {2i32};
    let _ = ghost! {
        proof_assert!(*g == 1i32);
    };
}

pub fn pa9() {
    let g = ghost! {0i32};
    {
        let mut g = ghost! {5i32};
        let _ = ghost! {
            *g = 1i32;
        };
    }
    let _ = ghost! {
        proof_assert!(*g == 1i32);
    };
}

pub fn pa10() {
    let mut g = ghost! {0i32};
    let g2 = ghost! {3i32};
    let _ = ghost! {
        *g = *g2;
    };
    let g = ghost! {4i32};
    let _ = ghost! {
        proof_assert!(*g == 3i32);
    };
}

#[requires(h@ == 1)]
pub fn cp2(h: i32) {
    let h = 2i32;
    let c = || h;
    let v = c();
    proof_assert!(v@ == 1);
}

#[requires(h@ == 1)]
pub fn cp3(h: i32) {
    let g = ghost! {h};
    let h = 2i32;
    let _ = ghost! {
        proof_assert!(*g == h);
    };
}

pub fn sb1() {
    let x = 1i32;
    {
        let x = 2i32;
        let _ = x;
    }
    proof_assert!(x == 2i32);
}

pub fn sb2(c: bool) {
    let x = 1i32;
    if c {
        let x = 5i32;
        let _ = x;
    }
    proof_assert!(x == 5i32);
}

pub fn sb3() {
    let x = 1i32;
    let y = x;
    let x = 2i32;
    proof_assert!(x == y);
}

pub fn sb4() {
    let x = 1i32;
    let mut i = 0i32;
    while i < 1 {
        let x = 3i32;
        let _ = x;
        i += 1;
    }
    proof_assert!(x == 3i32);
}

pub fn sb5() {
    let x = 1i32;
    {
        let x = 2i32;
        proof_assert!(x == 1i32);
    }
}
