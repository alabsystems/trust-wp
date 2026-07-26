// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(proc_macro_hygiene)]
#![allow(unexpected_cfgs)]

//! Regression fixture for #2209 / #1581: `Perm::disjoint_lemma` facts must
//! remain connected to the wrapped ghost permission locals seen by proof_assert!.

use trust_wp::{ghost, proof_assert};
use trust_wp_std::ghost::perm::Perm;

fn perm_disjoint_verify() {
    let (p1, mut own1) = Perm::new(0i32);
    let (p2, own2) = Perm::new(1i32);

    ghost! {
        let _ = Perm::disjoint_lemma(&mut own1, &own2);
    };

    proof_assert!(own1 != own2);
    proof_assert!(p1 != p2);
}

fn main() {
    perm_disjoint_verify();
}
