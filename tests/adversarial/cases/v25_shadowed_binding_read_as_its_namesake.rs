//@ expect: reject
//@ mechanism: a fact or a value about one binding was stated by its source NAME and read at the
//@ mechanism: assertion as the binding the name denotes THERE. A shadowing `let` (rs1, rs7), an
//@ mechanism: inner block's, a branch's or a loop body's `let` (rs14, rr3, rr4) bound the same
//@ mechanism: name to a new local: the clone fact `r2 == r` (the old `r`) was read about the new
//@ mechanism: `r`, because FactScope's written-since test asks about the old LOCAL, which nothing
//@ mechanism: writes. gs3: the ghost write `*g = *h` lowered to a store whose value is the old
//@ mechanism: `h`, translated as `Var("h")`, which the assertion's substitution then read as the
//@ mechanism: visible `h`. Every binding of a name a body binds more than once is now named apart
//@ mechanism: in `mir_built` and the assertion's names are resolved at its source scope (D-237).
//@ accept-means: a fact about one binding is read as a fact about another binding of its name.
//@ WHY THE CONTRACT IS FALSE: rs1: r holds 2, r2 holds 1. rs7: the same with Arc. rs14, rr3, rr4:
//@ WHY THE CONTRACT IS FALSE: the inner r holds 2 or 3, r2 holds 1. gs3: g holds 7, the visible h
//@ WHY THE CONTRACT IS FALSE: holds 9. rn1 is the shape with no clone: it never verified.
//@ fixed-by: D-237
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): before D-237 the assertions of
//@ teeth: rs1, rs7, rs14, rr3, rr4 and gs3 VERIFIED; with D-237 all FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use ::std::rc::Rc;
use ::std::sync::Arc;
use creusot_std::prelude::*;

pub fn rs1() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    let r = Rc::new(2i32);
    proof_assert!(r == r2);
}

pub fn rs7() {
    let a = Arc::new(1i32);
    let a2 = a.clone();
    let a = Arc::new(2i32);
    proof_assert!(a == a2);
}

pub fn rs14() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    {
        let r = Rc::new(2i32);
        proof_assert!(r == r2);
    }
}

pub fn rr3(c: bool) {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    if c {
        let r = Rc::new(3i32);
        proof_assert!(r == r2);
    }
}

pub fn rr4() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    let mut i = 0i32;
    while i < 1 {
        let r = Rc::new(3i32);
        proof_assert!(r == r2);
        i += 1;
    }
}

pub fn gs3() {
    let mut g = ghost! {0i32};
    let h = ghost! {7i32};
    let _ = ghost! {
        *g = *h;
    };
    let h = ghost! {9i32};
    let _ = ghost! {
        proof_assert!(*g == *h);
    };
}

pub fn rn1() {
    let r = Rc::new(1i32);
    let r2 = Rc::new(1i32);
    let r = Rc::new(2i32);
    proof_assert!(r == r2);
}
