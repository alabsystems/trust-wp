//@ expect: reject
//@ verdict: failed
//@ fn-failed: push_claims_two
//@ mechanism: the false twin of vec_push_len_old_spelling_control. A push adds one element, so
//@ mechanism: the length the pre-Creusot spelling states, entry plus two, is never the length `v`
//@ mechanism: is left with. It guards the reading that lets the control verify: if the unwrapped
//@ mechanism: `v@` were read at entry, or `old(..)` at exit, or the push's own spec dropped, a
//@ mechanism: length claim would no longer be tied to the one push.
//@ WHY THE CONTRACT IS FALSE: any call; `v` empty at entry is left with one element, not two.
//@ fixed-by: n/a (guards a completeness gain; no build is known to have accepted it)
//@ accept-means: the length a push leaves is not tied to the length it found.
//@ teeth: UNVERIFIED as a gate: no build is known to accept it. MEASURED FAILED with a
//@ teeth: counterexample on the campaign head, as its true twin verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(v@.len() == old(v@.len()) + 2)]
pub fn push_claims_two(v: &mut Vec<i32>, val: i32) {
    v.push(val);
}
