//@ expect: reject
//@ mechanism: capturing closure's environment tuple1(b) substituted for err(); payload compared as an Int.
//@ fixed-by: wp-s23 exact-thunk rule + opaque-callable clause drop
//@ accept-means: the Err payload was taken to be the captured b itself; it is b+1, neither b nor b+2
//@ teeth: defense in depth — the Int-payload form was NOT accepted before the fix (FAILED on the 0989c2e driver); the audit accept of the Err(b)||Err(b+2) form rested also on whole-Result equality. Kept so the payload route never regresses
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// FALSE: e = b + 1.
pub fn capture_ok_or_else_payload(b: i32) {
    if b < 100 {
        let n: Option<i32> = None;
        let r = n.ok_or_else(move || b + 1);
        match r {
            Err(e) => proof_assert!(e@ == b@ || e@ == b@ + 2),
            Ok(_) => {}
        }
    }
}
