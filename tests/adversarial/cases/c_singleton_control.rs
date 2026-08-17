//@ expect: verify
//@ mechanism: singleton-carrier collapse — the exclusivity law that the collapse makes
//@ mechanism: CONTRADICTORY (forced x == y refutes distinct ids, so the base goes vacuous and the
//@ mechanism: proof is demoted rather than accepted)
//@ fixed-by: a224bb2 (resfid)
//@ accept-means: n/a (control) — this contract is TRUE and is the shape resfid un-demoted.
//@
//@ Pre-resfid this rejected: the forced singleton made `mid(x) = a0 != a1 = mid(y)` unsatisfiable,
//@ so the base was genuinely UNSAT and the vacuity check demoted the proof. The adversarial twin
//@ (c_singleton_collapse_identity) is the same defect seen from the accept side.
//@ teeth: ★VERIFIED (opposite direction). Same knob: this control ERRORS with the gate disabled —
//@ teeth: the forced singleton makes the distinct-id premise contradictory, the base goes UNSAT and
//@ teeth: the vacuity check demotes the proof. Both halves of the mechanism reproduce.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{ghost::resource::Resource, logic::ra::excl::Excl, prelude::*};

#[ensures(x.id() != y.id())]
#[ensures(*x == ^x)]
pub fn ids_are_distinct(x: &mut Resource<Excl<i32>>, y: &Resource<Excl<i32>>) {
    if x.id_ghost() == y.id_ghost() {
        // Two exclusive resources with the same id cannot both be valid.
        x.valid_op_lemma(y);
        assert!(false);
    }
}
