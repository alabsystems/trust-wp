//@ expect: verify
//@ mechanism: control for v25_shadowed_binding_read_as_its_namesake.rs and
//@ mechanism: v25_shadowed_parameter_and_clone_reads.rs: true claims across shadowing, each name
//@ mechanism: read as the binding it denotes at the assertion (D-237). va2: the clone fact of the
//@ mechanism: first `r` read as `r2`'s value. va6: `let r = r.clone();` whose receiver is the
//@ mechanism: binding it shadows. ok1/ok2/va1/va3/va5: a shadowed name read inside and after the
//@ mechanism: block that shadows it, a copy taken before the shadow, a parameter re-bound, an
//@ mechanism: invariant over unshadowed names, a `let` reading the binding it shadows.
//@ accept-means: n/a (control) - every assertion holds.
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): before D-237 the assertions of
//@ teeth: va2 and va6 FAILED (one name stood for both receivers); with D-237 every one VERIFIED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use ::std::rc::Rc;
use creusot_std::prelude::*;

pub fn ok1() {
    let x = 1i32;
    {
        let x = 2i32;
        proof_assert!(x == 2i32);
    }
    proof_assert!(x == 1i32);
}

pub fn ok2() {
    let x = 1i32;
    let y = x;
    let x = 2i32;
    proof_assert!(x == y + 1i32);
}

#[requires(x@ > 0)]
pub fn va1(x: i32) {
    let x = 0i32;
    proof_assert!(x@ == 0);
}

pub fn va2() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    let r = Rc::new(2i32);
    let _ = r;
    proof_assert!(*r2 == 1i32);
}

pub fn va3() {
    let mut i = 0i32;
    let n = 10i32;
    #[invariant(i@ <= n@)]
    while i < n {
        i += 1;
    }
    proof_assert!(i@ <= n@);
}

pub fn va5() {
    let x = 1i32;
    let x = x + 1;
    proof_assert!(x == 2i32);
}

pub fn va6() {
    let r = Rc::new(1i32);
    let r = r.clone();
    proof_assert!(*r == 1i32);
}
