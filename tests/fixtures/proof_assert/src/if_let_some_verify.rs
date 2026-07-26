// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! proof_assert inside `if let Some(b) = ...` block.
//!
//! The MIR for `if let Some(b) = Some(true)` uses discriminant reads and
//! downcast projections. The extraction pipeline must handle:
//! 1. `Rvalue::Discriminant` (opaque → SwitchInt fallback explores all arms)
//! 2. `ProjectionElem::Downcast` (no-op in expression model)
//! 3. `Field(0)` on the downcasted value (identity passthrough for scalars)
//!
//! Re: #746

use trust_wp::proof_assert;

fn if_let_some_verify() -> bool {
    if let Some(b) = Some(true) {
        proof_assert!(b);
        b
    } else {
        false
    }
}

fn main() {
    let _ = if_let_some_verify();
}
