//@ expect: verify
//@ xfail: the arm is unreachable under the precondition, and the marker that pairs with its goal
//@ xfail: is not counted, but the call with no spec in the arm is assumed to return `true` and the
//@ xfail: proof is demoted for it (`opaque_call_true_assumption`), identically on the build before
//@ xfail: the pairing. Retire this directive when a panic's message call is modelled.
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of panic_msg_arm_reachable: `#[requires(flag)]` makes the panic arm
//@ mechanism: unreachable. Pinned `unknown` so that reading the pair as a refutation — a FAILED on
//@ mechanism: this program — fails the corpus (D-141).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(flag)]
pub fn diverging(flag: bool) {
    let y = if flag {
        1i32
    } else {
        panic!("flag was false");
    };
    proof_assert!(y == 1i32);
}
