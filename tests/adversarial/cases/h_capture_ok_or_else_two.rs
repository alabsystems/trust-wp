//@ expect: reject
//@ mechanism: capturing closure translated to its environment tuple and substituted for err() in ok_or_else's contract.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: two different capturing closures were identified by their equal environments (b); the payloads are b+1 and b+2
//@ teeth: verified — ACCEPTED (EXIT=0) before the fix (audit probe on the capturing-closure environment shape)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: e1 = b + 1, e2 = b + 2.
pub fn capture_ok_or_else_two(b: i32) {
    if b < 100 {
        let n: Option<i32> = None;
        let r1 = n.ok_or_else(move || b + 1);
        let r2 = n.ok_or_else(move || b + 2);
        match (r1, r2) {
            (Err(e1), Err(e2)) => proof_assert!(e1 == e2),
            _ => {}
        }
    }
}
