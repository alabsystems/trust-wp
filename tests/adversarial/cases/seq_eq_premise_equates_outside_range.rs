//@ expect: reject
//@ mechanism: Seq `==` is encoded as equality of the (array, length, offset) triple that
//@ mechanism: represents each side, guarded only by a non-zero length
//@ mechanism: (seq/coercion.rs try_decompose_seq_equality, the lane without a known length).
//@ mechanism: That is REPRESENTATION equality, strictly stronger than the extensional equality
//@ mechanism: Creusot means (Why3 seq: equal length and equal elements): two subsequences of one
//@ mechanism: sequence at different offsets share the array but not the offset, so they are
//@ mechanism: never equal, whatever their elements.
//@ mechanism: In a PREMISE the same encoding is not only possibly contradictory (which the
//@ mechanism: vacuity recheck catches) but CONSISTENT and too strong: equal length-1 prefixes
//@ mechanism: equate the two whole backing arrays and offsets, so every element past the prefix
//@ mechanism: is equated too, and nothing contradicts it.
//@ accept-means: an element outside the equated range was derived equal from a prefix equality.
//@ WHY THE CONTRACT IS FALSE: `s = [0, 1]` and `u = [0, 2]` satisfy the precondition and
//@ WHY THE CONTRACT IS FALSE: `s[1] != u[1]`.
//@ fixed-by: OPEN — committed RED with seq_eq_subsequence_offsets_disequality.
//@ teeth: ACCEPTED (exit 0) both at the review base and at the head it reviewed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(s.len() == 2 && u.len() == 2 && s.subsequence(0, 1) == u.subsequence(0, 1))]
#[ensures(s[1] == u[1])]
pub fn f(s: Ghost<Seq<Int>>, u: Ghost<Seq<Int>>) {}
