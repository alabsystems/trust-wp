//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: a borrowed place was frozen although it was mutated through its &mut alias
//@
//@ WHY THE ASSERTION IS FALSE: v holds one element after r.push(1).
//@ teeth: PROSPECTIVE — rejected on bc5554c and with the s31 freeze; guards the borrow-alias route (r is region-typed, v is reached through r's assignment).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn alias_push_wrong() {
    let mut v: Vec<i32> = Vec::new();
    let r = &mut v;
    r.push(1i32);
    proof_assert!(v@.len() == 0);
}
