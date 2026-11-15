// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `^` of an `if` or `match` one of whose branches is the shared borrow `&p`
//! has no reading. Each was read as `^p` and verified. The chained
//! comparison keeps the clause from the Rust type-check.

use trust_wp::{ensures, requires};

#[requires(*p < 100)]
#[ensures(^(if true { &p } else { p }) == old(*p) + 1 && 0 < 1 < 2)]
fn final_of_if_borrow(p: &mut i32) {
    *p += 1;
}

fn main() {}
