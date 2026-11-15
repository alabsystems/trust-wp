//@ expect: reject
//@ mechanism: capturing closure's environment substituted for f() in bool::then's contract; payload compared as an Int.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: bool::then(move || b + 1) was taken to yield Some(b); it yields Some(b+1)
//@ teeth: defense in depth — NOT accepted before the fix either (inconclusive quantifier-unhandled on the 0989c2e driver); the drop rule keeps it from ever resting on the env tuple
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: v = b + 1.
pub fn capture_bool_then(b: i32) {
    if b < 100 {
        let r = true.then(move || b + 1);
        match r {
            Some(v) => proof_assert!(v == b),
            None => {}
        }
    }
}
