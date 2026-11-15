// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `r` is `&p`, a shared reference, and `^` of it has no reading: the clause
//! was read as `^p`. The chained comparison keeps the clause from the Rust
//! type-check, so only trust-wp's own reading stands between it and a
//! verdict.

use trust_wp::{ensures, requires};

#[requires(*p < 100)]
#[ensures({ let r = &p; ^r == old(*p) + 1 && 0 < 1 < 2 })]
fn inc(p: &mut i32) {
    *p += 1;
}

fn main() {}
