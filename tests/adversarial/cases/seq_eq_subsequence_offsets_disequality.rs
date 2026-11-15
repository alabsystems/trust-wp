//@ expect: reject
//@ mechanism: Seq `==` is encoded as equality of the (array, length, offset) triple that
//@ mechanism: represents each side, guarded only by a non-zero length
//@ mechanism: (seq/coercion.rs try_decompose_seq_equality, the lane without a known length).
//@ mechanism: That is REPRESENTATION equality, strictly stronger than the extensional equality
//@ mechanism: Creusot means (Why3 seq: equal length and equal elements): two subsequences of one
//@ mechanism: sequence at different offsets share the array but not the offset, so they are
//@ mechanism: never equal, whatever their elements.
//@ accept-means: `s1 != s2` was proved from the offsets of the two subsequences, not from a
//@ accept-means: pair of differing elements.
//@ WHY THE CONTRACT IS FALSE: for `s = [7, 7, 7]` both subsequences are `[7, 7]`.
//@ fixed-by: OPEN — committed RED. A Seq equality between two terms whose triples are already
//@ fixed-by: fixed must compare elements over the length (the known-length lane already does).
//@ teeth: ACCEPTED (exit 0) both at the review base and at the head it reviewed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(s.len() == 3)]
#[ensures(s.subsequence(1, 3) != s.subsequence(0, 2))]
pub fn f(s: Ghost<Seq<Int>>) {}
