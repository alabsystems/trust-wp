// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression fixture for #816: proof_assert Phase 2 ICE on bool call specs.
//!
//! When a function returns bool and has predicate-style ensures, the
//! proof_assert path crashes with `BUG: mk_eq expects same sort, got Int = Bool`
//! because the call result variable gets Int sort instead of Bool sort.
//!
//! After the fix, this should produce a verification result (pass or fail)
//! without crashing.

use trust_wp::{ensures, proof_assert, requires};

#[requires(flag)]
#[ensures(flag)]
fn id_bool(flag: bool) -> bool {
    flag
}

fn bool_call_no_crash(flag: bool) {
    let _ = id_bool(flag);
    proof_assert!(flag);
}

fn main() {
    bool_call_no_crash(true);
}
