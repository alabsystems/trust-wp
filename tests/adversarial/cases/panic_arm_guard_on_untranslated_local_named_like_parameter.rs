//@ expect: reject
//@ mechanism: `on_assign_local` binds a destination whose right-hand side it cannot translate (here
//@ mechanism: `q as usize`, a pointer-to-integer cast) to `Var(<source name>)`, and a parameter's source
//@ mechanism: name is its entry-value symbol. The local `a` shadowing the parameter `a` is therefore the
//@ mechanism: parameter's value to the solver, so the path guard `!(a == 5)` of the parameter's early
//@ mechanism: return discharges the panic goal on the local: `!(a == 5) ==> !(a == 5)`.
//@ mechanism: `primary_arithmetic_is_exact` does not see an untranslated binding, so the charged edge is
//@ mechanism: proved dead (D-142), and the clause-free cap stops walking into the panic arm.
//@ accept-means: a clause-free body that panics when `q`'s address is 5 is credited `verified`, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(0, 5 as *const u8)` panics (a clause-free fn is checked under `requires true`).
//@ teeth: ACCEPTED with this front's charged-edge credit before D-169; at the campaign tip D-142's proved
//@ teeth: edge is withheld by D-143 and `f` is `unknown` (capped). With D-169 the charge is refuted: `f FAILED`.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: D-169 (an untranslated assignment is bound to a symbol of its own site).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(a: usize, q: *const u8) {
    if a == 5 {
        return;
    }
    let a = q as usize;
    if a == 5 {
        panic!()
    }
}
