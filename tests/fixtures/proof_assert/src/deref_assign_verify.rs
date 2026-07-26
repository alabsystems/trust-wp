// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! proof_assert after mutable dereference assignment.
//!
//! Tests that the extraction pipeline tracks deref writes (`*a = expr`)
//! and propagates them to proof_assert substitutions via `"*name"` entries.
//!
//! Re: #746 AC1

use trust_wp::{proof_assert, requires};

#[requires(*a >= 0)]
fn set_and_check(a: &mut i32) {
    *a = 1;
    proof_assert!(*a > 0);
}

fn main() {
    let mut x = 0;
    set_and_check(&mut x);
}
