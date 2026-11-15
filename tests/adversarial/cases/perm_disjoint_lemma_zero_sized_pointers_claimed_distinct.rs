//@ expect: reject
//@ mechanism: the builtin spec of `Perm::disjoint_lemma(own1, own2)` ensures `own1 != own2` for every
//@ mechanism: permission type, and `Perm::new` states the pointer it returns is its permission, so
//@ mechanism: two permissions give two distinct pointers. Creusot's lemma for `Perm<*const T>` is
//@ mechanism: `size_of_val(*own1.val()) != 0 && size_of_val(*own2.val()) != 0 ==> addr1 != addr2`:
//@ mechanism: two zero-sized values share an address. `Box::new(())` allocates nothing, so both
//@ mechanism: `Perm::new(())` pointers are the same dangling one.
//@ accept-means: a ghost lemma claims two pointers differ that are equal on every call; the
//@ accept-means: proof_assert proves a false equation about run-time values.
//@ fixed-by: D-139 — the lemma's fact holds only where the call site knows both containers are
//@ fixed-by: distinct: a pointee of non-zero size, or a trust-wp-std cell or atomic.
//@ teeth: ACCEPTED (`proof_assert in creusot_test::f verified`, exit 0) when committed. Natively
//@ teeth: the two `Box::into_raw(Box::new(()))` pointers are both `0x1`. FAILED under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() {
    let (p1, mut own1) = Perm::new(());
    let (p2, own2) = Perm::new(());
    ghost! {
        let _ = Perm::disjoint_lemma(&mut own1, &own2);
    };
    proof_assert!(p1 != p2);
}
