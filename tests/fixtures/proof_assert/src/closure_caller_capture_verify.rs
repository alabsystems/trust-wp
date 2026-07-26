// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(proc_macro_hygiene)]
#![allow(unexpected_cfgs)]

//! Regression fixture for #1489 (closure Layer 2).
//!
//! After a direct FnMut closure call, the caller must be able to observe
//! capture state updates via `proof_assert!`. This tests the
//! `enrich_direct_closure_postconditions` enrichment path.

use trust_wp::{ensures, proof_assert, requires};

/// Direct FnMut call: the closure increments `x`, and the caller's
/// proof_assert checks the post-call value.
#[requires(x == 10i32)]
pub fn direct_fnmut_call(mut x: i32) {
    let mut c = {
        #[requires(x < 1_000_000i32)]
        #[ensures(x == old(x) + 1i32)]
        || {
            x += 1;
            5
        }
    };
    c();
    proof_assert!(x == 11i32);
}

/// Two direct FnMut calls: mirrors test_fnmut from 07_mutable_capture.
/// After c() is called twice, x should have incremented by 2.
#[requires(x == 10i32)]
pub fn direct_fnmut_two_calls(mut x: i32) {
    let mut c = {
        #[requires(x < 1_000_000i32)]
        #[ensures(x == old(x) + 1i32)]
        || {
            x += 1;
            5
        }
    };
    c();
    c();
    proof_assert!(x == 12i32);
}

/// Exact mirror of test_fnmut from 07_mutable_capture.rs — uses u32 and x@ (view).
#[requires(x@ == 100_000i64)]
pub fn test_fnmut_mirror(mut x: u32) {
    let mut c = {
        #[requires(x@ < 1_000_000i64)]
        #[ensures(x@ == old(x@ + 1i64))]
        || {
            x += 1;
            5
        }
    };
    c();
    c();
    proof_assert!(x@ == 100_002i64);
}

fn main() {
    direct_fnmut_call(10);
    direct_fnmut_two_calls(10);
    test_fnmut_mirror(100_000);
}
