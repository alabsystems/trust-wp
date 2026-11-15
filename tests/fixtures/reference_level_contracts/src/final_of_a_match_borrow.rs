// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `^` of a `match` whose arm is the shared borrow `&p` has no reading. It
//! was read as `^p` and verified.

use trust_wp::{ensures, requires};

#[requires(*p < 100)]
#[ensures(^(match 0 { _ => &p }) == old(*p) + 1 && 0 < 1 < 2)]
fn final_of_match_borrow(p: &mut i32) {
    *p += 1;
}

fn main() {}
