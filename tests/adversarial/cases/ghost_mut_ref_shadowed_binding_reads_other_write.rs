//@ expect: reject
//@ mechanism: two `&mut` bindings that share a source name share the symbol of their current value. The
//@ mechanism: `Some(x)` of `get_mut_ghost(&1)` is written on its arm (`*x = 43`); the later `x` of
//@ mechanism: `split_mut_ghost(&2)` points at another entry and is only read. Both are spelled `x_current`
//@ mechanism: once lowered, so the arm's write is a premise about the second binding: the solver proves
//@ mechanism: `*x == 43` (UNSAT), where its renamed twin (`let (y, _) = ..; proof_assert!(*y == 43i32)`) and
//@ mechanism: the true assertion `*x == 5i32` both get a counterexample. The credit is withheld only by
//@ mechanism: strict certification: `proof_assert .. evidence gap (certificate derivation mismatch at
//@ mechanism: ordinal 2: expected NativeEncoded, got ExactPreparedPremise)`, at the campaign tip and with
//@ mechanism: D-169 alike. The same sharing makes should_succeed ghost/ghost_map.rs contradictory: its two
//@ mechanism: `x` bindings are written 43 and 42 (`x_current == 43`, `x_current == 42`), and with D-169
//@ mechanism: `ghost_map` is reported `vacuous (contradictory premises)` (the campaign tip: `unknown`,
//@ mechanism: quantifier instantiation incomplete); cut down to the two writes under `ensures(false)` it
//@ mechanism: is vacuous with D-169 and refuted once the second binding is renamed. D-169's site symbols
//@ mechanism: cover an untranslated assignment, not a translated `&mut` binding.
//@ accept-means: a `proof_assert!` about one `&mut` binding is credited from a write made through another
//@ accept-means: binding of the same name, on an arm the assertion does not depend on.
//@ WHY THE CONTRACT IS FALSE: after the two inserts key 2 maps to 5 and the arm writes key 1 only, so the
//@ WHY THE CONTRACT IS FALSE: `x` that `split_mut_ghost(&2)` returns points at 5.
//@ teeth: UNVERIFIED as an accept: rejected at the campaign tip and with D-169, by the certificate check
//@ teeth: alone. The case pins that the assertion is not credited while the sharing stands.
//@ verdict: unknown
//@ timeout: 300
//@ fixed-by: open (a translated `&mut` binding's current value needs a symbol per binding).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{logic::FMap, prelude::*};

pub fn ghost_map() {
    let mut map = FMap::<i32, i32>::new();
    ghost! {
        map.insert_ghost(1, 21);
        map.insert_ghost(2, 5);
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        let (x, _map2) = map.split_mut_ghost(&2);
        proof_assert!(*x == 43i32);
    };
}
