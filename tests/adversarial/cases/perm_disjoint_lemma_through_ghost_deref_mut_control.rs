//@ expect: verify
//@ xfail: `own1 != own2` after `Perm::disjoint_lemma(&mut own1, &own2)` inside `ghost!` is not
//@ xfail: proved (`unknown (incomplete)`), and `foo` is partial on its unchecked ghost calls. The
//@ xfail: lemma's `&mut own1` goes through `DerefMut::deref_mut` on the ghost handle, and since
//@ xfail: K1's forwarding quarantine was deleted the write flows back to `own1`; D-8 names this
//@ xfail: program, the compat row ghost/disjoint_raw_ptr.rs, in the price of that deletion. The
//@ xfail: trust_wp_std spelling of it, the driver fixture ghost_perm_disjoint_verify, has both
//@ xfail: assertions refused as vacuous. Retire this directive when the lemma's fact reaches the
//@ xfail: permission the flow-back leaves in `own1`.
//@ xfail: The pin below is not met in every run: when several cases run at once, `p1 != p2` is
//@ xfail: sometimes refuted, here and in perm_disjoint_lemma_sized_pointers_distinct_control, on a
//@ xfail: smaller query than the one that verifies it and with a model ay validates; no run alone
//@ xfail: has refuted it. That refutation of a TRUE assertion is the defect the pin reports, and it
//@ xfail: is open.
//@ xfail-verdict: unknown
//@ mechanism: the TRUE program of the driver's ghost_perm_disjoint_verify fixture in the corpus's
//@ mechanism: spelling: two live `Perm`s of an `i32` are two permissions and two addresses.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

pub fn foo() {
    let (p1, mut own1) = Perm::new(1i32);
    let (p2, own2) = Perm::new(1i32);

    ghost! {
        let _ = Perm::disjoint_lemma(&mut own1, &own2);
    };
    proof_assert!(own1 != own2);
    proof_assert!(p1 != p2);
}
