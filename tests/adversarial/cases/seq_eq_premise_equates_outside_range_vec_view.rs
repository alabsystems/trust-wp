//@ expect: reject
//@ mechanism: Seq `==` is encoded as equality of the (array, length, offset) triple that
//@ mechanism: represents each side, guarded only by a non-zero length
//@ mechanism: (seq/coercion.rs try_decompose_seq_equality, the lane without a known length).
//@ mechanism: That is REPRESENTATION equality, strictly stronger than the extensional equality
//@ mechanism: Creusot means (Why3 seq: equal length and equal elements): two subsequences of one
//@ mechanism: sequence at different offsets share the array but not the offset, so they are
//@ mechanism: never equal, whatever their elements.
//@ mechanism: seq_eq_premise_equates_outside_range over two `Vec` views.
//@ accept-means: an element outside the equated range was derived equal from a prefix equality.
//@ WHY THE CONTRACT IS FALSE: `v = vec![0, 1]`, `u = vec![0, 2]` satisfy the precondition and
//@ WHY THE CONTRACT IS FALSE: `v[1] != u[1]`.
//@ fixed-by: OPEN — committed RED with seq_eq_subsequence_offsets_disequality.
//@ teeth: ACCEPTED (exit 0) both at the review base and at the head it reviewed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 2 && u@.len() == 2 && v@.subsequence(0, 1) == u@.subsequence(0, 1))]
#[ensures(v@[1] == u@[1])]
pub fn f(v: &Vec<u32>, u: &Vec<u32>) {}
