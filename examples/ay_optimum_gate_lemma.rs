// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// AUTHORED-PENDING (trust-wp): Creusot-syntax contract for the AY OPTIMUM gate
// soundness lemma, mirroring the real gate in `ay/crates/ay-pb/src/portfolio.rs`
// and the LB in `cdcl.rs::objective_lower_bound_from_constraints`.
//
// STATUS: NOT discharged here. trust-wp pins channel="trust" (the self-hosted
// Trust rustc fork) and links rustc_private; that sysroot is not built in this
// environment (multi-hour from-source bootstrap), so the trust-wp driver cannot
// run. The companion target — eval_constraint i128 faithfulness — is
// deliberately NOT routed to trust-wp: trust-wp's type-erased `Sort::Int` cannot
// observe i128 wraparound, so the overflow-safety obligation would verify
// vacuously. That obligation is discharged on BV128 by trust-vc instead (see
// `ay/crates/ay-pb/proofs/trust_vc/gate_and_eval_lemmas.rs`, DISCHARGED).
//
// The gate lemma below is pure integer-order transitivity, which IS sound under
// Sort::Int, so trust-wp could discharge it once the Trust toolchain is built.
// Run (after building the Trust toolchain):
//   ./scripts/run-trust-wp-rustc.sh examples/ay_optimum_gate_lemma.rs -- --force

use trust_wp::{ensures, requires};

/// OPTIMUM gate soundness, Skolemized per feasible point.
///
/// `value`  = objective of a re-verified FEASIBLE incumbent.
/// `floor`  = a SOUND lower bound: for every feasible x, `floor <= objective(x)`.
/// `obj_x`  = objective of an ARBITRARY feasible point (universally quantified by
///            the contract's free parameter).
///
/// `requires(value <= floor)` is the gate guard; `requires(floor <= obj_x)` is
/// the sound-LB hypothesis at that point. The postcondition states the incumbent
/// value lower-bounds every feasible objective — i.e. it is the global optimum
/// (it is also attained, by the incumbent itself).
#[requires(value <= floor)]
#[requires(floor <= obj_x)]
#[ensures(result == true)]
#[ensures(value <= obj_x)]
fn optimum_gate_sound(value: i128, floor: i128, obj_x: i128) -> bool {
    value <= floor
}

fn main() {
    assert!(optimum_gate_sound(3, 5, 9));
}
