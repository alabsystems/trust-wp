//@ expect: verify
//@ xfail: measured `unknown (incomplete)`. The `Option<&mut V>` carrier that `get_mut_ghost`
//@ xfail: returns in scrutinee position is not solvable in this lane today; R4 refuses to pin, so
//@ xfail: the honest containment fact cannot be produced. Re-entry is the R4 closure itself.
//@ mechanism: R4 (`root_unnamed`) — over-refusal control for `g_r4_none_branch_pin`
//@ fixed-by: n/a (open; blocked on the R4 closure)
//@ accept-means: n/a (control). An XPASS is the signal that R4 was closed AND the guard is real;
//@ accept-means: when it happens, `g_r4_none_branch_pin` MUST still reject — check both together.
//@ accept-means: This pair is the whole point: the two bodies are byte-identical apart from the
//@ accept-means: `#[requires]`, so only a guard that actually depends on the branch condition can
//@ accept-means: separate them. A fix that accepts both is a false accept; a fix that rejects both
//@ accept-means: has closed nothing.
//@
//@ WHY THE CONTRACT IS TRUE: the precondition forces the `Some` branch — `GET_MUT_GHOST` ensures
//@ `None => !self.contains(*k)`, which contradicts `map.contains(1)` — and its `Some` arm then
//@ gives `(^self).contains(*k)` directly. No prophecy on the payload is needed.
//@ teeth: n/a — over-refusal control, currently xfail. Not demonstrated in either direction.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::FMap, prelude::*};

#[requires(map.contains(1i32))]
pub fn none_branch_honest(mut map: FMap<i32, i32>) {
    ghost! {
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        proof_assert!(map.contains(1i32));
    };
}
