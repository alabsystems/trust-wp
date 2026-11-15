//@ expect: verify
//@ mechanism: control — the creusot_std spelling of the driver's snapshot_block_seq_mapping_closure
//@ mechanism: fixture: a `snapshot!` block binding two local closures and returning `seq![..]`, read
//@ mechanism: as the logical sequence it builds. Its trust_wp spelling is demoted on the four program
//@ mechanism: calls that spelling makes (snapshot_block_local_closures_seq_trust_wp_spelling_control.rs).
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{logic::Mapping, prelude::*};

#[ensures(true)]
pub fn snapshot_block_seq_mapping_closure_preserves_len() {
    let preds: Snapshot<Seq<Mapping<u32, bool>>> = snapshot! {
        let pred0 = |z: u32| z@ % 2 == 0;
        let pred1 = |z: u32| z@ % 2 == 1;
        seq![pred0, pred1]
    };

    proof_assert!(preds.len() == 2);
}
