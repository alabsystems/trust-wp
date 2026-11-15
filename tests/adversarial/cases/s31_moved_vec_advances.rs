//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: a moved-into Vec was frozen at its pre-push value
//@
//@ WHY THE ASSERTION IS FALSE: w holds one element after the push.
//@ teeth: PROSPECTIVE — rejected on bc5554c and with the s31 freeze; a freeze that identified the mutated place by the receiver EXPRESSION (Var(x) after `let mut y = x`) instead of MIR would freeze the mutated local and accept it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn move_then_push_wrong() {
    let v: Vec<i32> = Vec::new();
    let mut w = v;
    w.push(1i32);
    proof_assert!(w@.len() == 0);
}
