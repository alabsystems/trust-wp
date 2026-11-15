//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: value copies of a mutated receiver follow the mutation again
//@
//@ WHY THE ASSERTION IS FALSE: n is 0, v@.len() is 1 after the push.
//@ teeth: VERIFIED — accepted on 3bba620 (skeptic probe p1) and rejected with the s31 freeze; not re-run on bc5554c.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn len_push() {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    v.push(1i32);
    proof_assert!(n@ == v@.len());
}
