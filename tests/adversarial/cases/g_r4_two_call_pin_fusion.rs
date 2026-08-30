//@ expect: reject
//@ mechanism: R4 (`root_unnamed`) — TWO `get_mut_ghost` calls in one body. Targets pins keyed on
//@ mechanism: anything weaker than the individual borrow: the shared `Option<&mut V>` carrier sort's
//@ mechanism: payload projection, the callee's result slot, or a `(receiver, key)`-keyed restore
//@ mechanism: carrier. Any of those fuses the two payloads into one symbol.
//@ fixed-by: n/a (OPEN — R4 refuses to pin; prerequisite gate for closing it)
//@ accept-means: `^x` and `^y` — the payloads of two SEPARATE calls, borrowing two SEPARATE entries —
//@ accept-means: were conflated, so both pins land on one term and the last write wins for both
//@ accept-means: keys. This is the sibling-binder fusion that produced the adjudicated
//@ accept-means: `take_first_mut` false accept (`a2_sibling_binder_fusion`), and the same id-collapse
//@ accept-means: the restore-route audit closed when `__seq_index_restore_<carrier>(seq, idx)` turned
//@ accept-means: out to be a function of (carrier, index) ALONE. Relocated into the R4 lane, where
//@ accept-means: the two carriers are unnamed temporaries and therefore easiest to confuse.
//@
//@ WHY THE CONTRACT IS FALSE: the two arms write 43 to key 1 and 44 to key 2. `map.lookup(2)` is 44.
//@ Refutable by running `two_call_pin_fusion()`.
//@ teeth: PROSPECTIVE — NOT an A/B-demonstrated accept. Measured today: rejected in 2s,
//@ teeth: `proof_assert ... inconclusive (quantifier-ematching-exists-incomplete)` (runner verdict
//@ teeth: `error`) — rejected trivially: R4 emits no pin, so there is nothing yet that could fuse.
//@ teeth: WHAT A WRONG R4 FIX MUST DO TO START ACCEPTING THIS: close R4 by naming the carrier with
//@ teeth: anything that is not per-call — the payload accessor of the `Option<__trust_wp_mutref>`
//@ teeth: sort, a name derived from the callee `DefId`, or a receiver+key-keyed slot. All three are
//@ teeth: tempting precisely BECAUSE the carrier is an unnamed temporary and a stable name has to be
//@ teeth: invented; inventing one that two call sites share makes `^x == ^y` and proves this. The
//@ teeth: correct key is the individual borrow (the call's own destination local), which is what
//@ teeth: `projected_expiry`'s R0/R1 unique-assignment conditions already establish per candidate.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::FMap, prelude::*};

pub fn two_call_pin_fusion() {
    let mut map = FMap::<i32, i32>::new();
    ghost! {
        map.insert_ghost(1, 21);
        map.insert_ghost(2, 22);
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        if let Some(y) = map.get_mut_ghost(&2) {
            *y = 44;
        }
        proof_assert!(map.lookup(2i32) == 43i32);
    };
}
