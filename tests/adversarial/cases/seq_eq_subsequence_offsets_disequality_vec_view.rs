//@ expect: reject
//@ mechanism: Seq `==` is encoded as equality of the (array, length, offset) triple that
//@ mechanism: represents each side, guarded only by a non-zero length
//@ mechanism: (seq/coercion.rs try_decompose_seq_equality, the lane without a known length).
//@ mechanism: That is REPRESENTATION equality, strictly stronger than the extensional equality
//@ mechanism: Creusot means (Why3 seq: equal length and equal elements): two subsequences of one
//@ mechanism: sequence at different offsets share the array but not the offset, so they are
//@ mechanism: never equal, whatever their elements.
//@ mechanism: This is the same shape over a `Vec`'s view, the carrier the `Vec::into_iter` spec
//@ mechanism: (`self@ == result@`) and the view-identity component sharing both lean on.
//@ accept-means: `v@.subsequence(1, 3) != v@.subsequence(0, 2)` was proved from offsets alone.
//@ WHY THE CONTRACT IS FALSE: for `v = vec![7, 7, 7]` both subsequences are `[7, 7]`.
//@ fixed-by: OPEN — committed RED with seq_eq_subsequence_offsets_disequality.
//@ teeth: ACCEPTED (exit 0) both at the review base and at the head it reviewed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(v@.len() == 3)]
#[ensures(v@.subsequence(1, 3) != v@.subsequence(0, 2))]
pub fn f(v: &Vec<u32>) {}
