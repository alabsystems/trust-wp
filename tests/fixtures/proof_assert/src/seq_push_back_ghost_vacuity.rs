// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

//! Canary for #2616: ghost Seq mutation currently demotes a nontrivial
//! proof_assert to `unknown (vacuous proof ...)`.
//!
//! Carrier preservation (3bbe9f8) keeps `^call_4` symbolic, but additional
//! ghost-helper spec injection is still needed before this proof_assert
//! verifies.

use trust_wp::*;

fn seq_push_back_ghost_vacuity() {
    let _ = ghost! {
        let mut v = Seq::new();
        v.push_back_ghost(30i32);
        proof_assert!(v[0] == 30i32);
    };
}

fn main() {
    seq_push_back_ghost_vacuity();
}
