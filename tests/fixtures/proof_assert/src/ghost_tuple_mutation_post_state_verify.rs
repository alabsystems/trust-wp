// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(proc_macro_hygiene)]
#![allow(unexpected_cfgs)]

//! Regression for #2533: ghost tuple mutation must preserve post-state facts.
//!
//! The proof_assert path must not collapse `p.0 = 4` through the pre-mutation
//! tuple literal and emit a contradictory `(2 == 4)` call assumption.

extern crate creusot_std;
use creusot_std::prelude::*;

fn ghost_tuple_mutation_post_state_verify() {
    let mut p = ghost! {(2_i32, 3_i32)};

    let _ = ghost! {
        p.0 = 4;
    };

    let _ = ghost! {
        proof_assert!(p.0 == 4_i32);
        proof_assert!(p.1 == 3_i32);
    };
}

fn main() {
    ghost_tuple_mutation_post_state_verify();
}
