//@ expect: reject
//@ mechanism: receiver-state propagation advanced a Snapshot local equal to the receiver's
//@ mechanism: pre-state to the post-call prophecy, so the snapshot followed the mutation
//@ fixed-by: 3820919 (s25 vacuous whole-value equality)
//@ accept-means: snapshots are again rebound by later mutating calls
//@
//@ WHY THE ASSERTION IS FALSE: old is the empty sequence, v@ has one element.
//@ teeth: VERIFIED — accepted (verified, query was `(assert false)`) on cfff9b4, rejected with 3820919.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn snapshot_false() {
    let mut v: Vec<i32> = Vec::new();
    let old = snapshot!(v);
    v.push(1i32);
    proof_assert!(v@ == old@);
}
