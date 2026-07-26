// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Program-point extraction regression for proof_assert.
//!
//! The call postcondition (`result > 0`) is sufficient to verify `y > 0` at the
//! proof_assert site. A loop after the assertion should not force extraction to
//! model the tail of the function.
//!
//! Re: #746

use trust_wp::{ensures, proof_assert, requires};

#[requires(x > 0)]
#[ensures(result > 0)]
fn identity_positive(x: i32) -> i32 {
    x
}

fn callspec_before_unsupported_tail() -> i32 {
    let y = identity_positive(1);
    proof_assert!(y > 0);

    // Keep unsupported tail MIR after the proof_assert program point.
    let mut i = 0;
    while i < 2 {
        i += 1;
    }

    y
}

fn main() {
    let _ = callspec_before_unsupported_tail();
}
