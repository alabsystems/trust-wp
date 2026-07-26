// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(proc_macro_hygiene)]
#![allow(unexpected_cfgs)]

//! Regression fixture for #1190.
//!
//! Closure-body `proof_assert!` checks that depend on mutable capture updates
//! must use program-point substitutions from the closure body owner.

use trust_wp::{ensures, proof_assert, requires, trusted};

pub fn mutable_capture() {
    let mut x = 1;
    (#[requires(x == 1i32)]
    || {
        proof_assert!(x == 1i32);
        x = 2;
        proof_assert!(x == 2i32);
    })();
}

#[trusted]
#[requires(f.precondition(()))]
#[ensures(f.postcondition_once((), ()))]
fn calls_closure<F: FnOnce() -> ()>(f: F) {
    f();
}

pub fn captures_and_call() {
    let mut x = 1;
    let clos = #[requires(x == 1i32)]
    #[ensures(x == 2i32)]
    || {
        proof_assert!(x == 1i32);
        x = 2;
        proof_assert!(x == 2i32);
    };
    calls_closure(clos);
}

fn main() {
    mutable_capture();
    captures_and_call();
}
