//@ expect: reject
//@ mechanism: Rc/Arc view-sort hijack — an unfiltered Rc/Arc AdtDecl makes `rc@` resolve at the
//@ mechanism: CARRIER sort instead of the canonical Int model, and `rc@ == <lit>` becomes
//@ mechanism: eq(Rc, Int) -> a fresh unconstrained coercion variable
//@ fixed-by: 197ed3e (peel Rc/Arc in ADT collection, Box treatment in collect_adt_decls_from_ty)
//@ accept-means: the Rc identity/view premises were replaced by something that PROVES a pointer
//@ accept-means: equality between two distinct allocations. Under the adjudicated hijack the
//@ accept-means: model MERGED rc and rc3; if a future change turns that model-level merge into a
//@ accept-means: derivable equality (e.g. by assuming the coercion), this case accepts.
//@
//@ WHY THE CONTRACT IS FALSE: `a` and `b` are two separate `Rc::new` allocations, so
//@ `Rc::ptr_eq(&a, &b)` is false at run time.
//@ teeth: UNVERIFIED (honest, and structurally so). Method (ii): both halves of 197ed3e disabled
//@ teeth: in-tree (driver Rc/Arc peel + encoder canonical-Int fail-safe). This case still rejects
//@ teeth: (error). Premise fabrication is premise WEAKENING: it can never make a false goal provable.
//@ teeth: The teeth for this mechanism live in b_rc_view_control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use ::std::rc::Rc;
use creusot_std::prelude::*;

pub fn rc_ptr_eq_false_claim() {
    let a = Rc::new(0i32);
    let b = Rc::new(1i32);
    proof_assert!(*a@ == 0i32);
    proof_assert!(*b@ == 1i32);
    let same = Rc::ptr_eq(&a, &b);
    proof_assert!(same);
}
