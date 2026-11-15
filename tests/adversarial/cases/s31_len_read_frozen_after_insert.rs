//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: value copies of a mutated receiver follow the mutation again
//@
//@ WHY THE ASSERTION IS FALSE: n is 0, v@.len() is 1 after the insert.
//@ teeth: VERIFIED — accepted on bc5554c (pre-fix build of wp-s31), rejected with the s31 freeze.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn len_insert() {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    v.insert(0, 7i32);
    proof_assert!(n@ == v@.len());
}
