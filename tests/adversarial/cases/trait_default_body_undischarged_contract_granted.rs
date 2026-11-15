//@ expect: reject
//@ mechanism: a trait method's DEFAULT body fails the trait-level contract, and the type that
//@ mechanism: uses the default is handed that contract anyway. The credit ledger records an
//@ mechanism: undischarged trait contract only for an IMPL item (`granted_trait_method_of`
//@ mechanism: asks for `trait_item_def_id`, which a trait's own item does not have), so the
//@ mechanism: default body's FAILED verdict seeds nothing: `gen_read` (handed `Rd::rd` at a
//@ mechanism: generic call site), `go` (one call away) and `go_direct` (calling `W.rd()`,
//@ mechanism: which runs the default) all keep their credits. `impl Rd for W {}` runs exactly
//@ mechanism: the body that failed, so the contract is undischarged for W as surely as an
//@ mechanism: overriding impl that returned false would leave it.
//@ fixed-by: D-94 (a contracted trait method's default body owes the contract it declares)
//@ accept-means: `go` and `go_direct` claim `result` and both return false; `gen_read` holds a trait grant whose only implementation in the crate refuted it.
//@ teeth: MEASURED on the call-graph withdrawal walk alone: `Rd::rd FAILED` and `gen_read`, `go`, `go_direct` stand `verified ✓` with no withdrawal line. The isolating twin trait_default_body_undischarged_contract_granted_discharged_control.rs differs only in the default body returning true and verifies all four.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool {
        false
    }
}

// Uses the default body: the code that runs for `W` is the body that failed.
impl Rd for W {}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    gen_read::<W>(&W)
}

#[ensures(result)]
pub fn go_direct() -> bool {
    W.rd()
}
