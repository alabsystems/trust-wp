//@ expect: reject
//@ mechanism: Seq `==` is encoded as equality of the (array, length, offset) triple that
//@ mechanism: represents each side, guarded only by a non-zero length
//@ mechanism: (seq/coercion.rs try_decompose_seq_equality, the lane without a known length).
//@ mechanism: That is REPRESENTATION equality, strictly stronger than the extensional equality
//@ mechanism: Creusot means (Why3 seq: equal length and equal elements): two subsequences of one
//@ mechanism: sequence at different offsets share the array but not the offset, so they are
//@ mechanism: never equal, whatever their elements.
//@ mechanism: Here the equality is the body of an open logic function, unfolded at the use.
//@ accept-means: the unfolded logic body's Seq equality was evaluated as representation equality.
//@ WHY THE CONTRACT IS FALSE: `s = [7, 7, 7]` makes `same_tail(s)` true.
//@ fixed-by: OPEN — committed RED with seq_eq_subsequence_offsets_disequality.
//@ teeth: ACCEPTED (exit 0) both at the review base and at the head it reviewed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic(open)]
pub fn same_tail(s: Seq<Int>) -> bool {
    pearlite! { s.subsequence(1, 3) == s.subsequence(0, 2) }
}

#[requires(s.len() == 3)]
#[ensures(!same_tail(*s))]
pub fn f(s: Ghost<Seq<Int>>) {}
