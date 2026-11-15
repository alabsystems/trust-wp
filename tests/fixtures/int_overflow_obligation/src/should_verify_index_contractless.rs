// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: a contract-free body whose arithmetic goal holds and whose index is
//! in bounds on every path. The bounds check is a charged obligation (D-95),
//! so the body is a target for it and verifies instead of being capped.

pub fn index_guarded(a: [u8; 4], i: usize) -> usize {
    if i < 4 {
        let _ = a[i];
        i + 1
    } else {
        0
    }
}

fn main() {}
