//@ expect: verify
//@ xfail: in the trust_wp spelling a `snapshot!` block that binds local closures and returns
//@ xfail: `seq!(..)` is rewritten to program calls (each closure becomes `Mapping::from_closure`,
//@ xfail: and `seq!` expands to `Seq::singleton` then `push_back`), and none of the four has a spec,
//@ xfail: so each reaches the opaque-call fallback, which owes `requires(false)` and demotes the
//@ xfail: function: `unknown (demoted: encoding approximations may affect soundness:
//@ xfail: opaque_call_true_assumption(4))`. The assertion over the captured sequence verifies, and the
//@ xfail: creusot_std spelling of the same block verifies
//@ xfail: (snapshot_block_local_closures_seq_creusot_spelling_control.rs). The price is this function's
//@ xfail: verdict. Retire this directive when those construction calls inside a snapshot are read as
//@ xfail: the logical values they build.
//@ mechanism: control — the driver's snapshot_block_seq_mapping_closure fixture, as a case.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp::{
    logic::{Mapping, Seq},
    *,
};

#[ensures(true)]
pub fn snapshot_block_seq_mapping_closure_preserves_len() {
    let preds: Snapshot<Seq<Mapping<u32, bool>>> = snapshot! {
        let pred0 = |z: u32| z@ % 2 == 0;
        let pred1 = |z: u32| z@ % 2 == 1;
        seq!(pred0, pred1)
    };

    proof_assert!(preds.len() == 2);
}
