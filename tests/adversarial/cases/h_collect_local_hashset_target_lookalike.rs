//@ expect: reject
//@ mechanism: collect roundtrip gate — (Self, B) identity must come from DefId provenance, never from a printed path
//@ fixed-by: wp-s24 (collect-hardening-v2, teeth v3)
//@ accept-means: the roundtrip was granted to a LOCAL lookalike std::collections::HashSet target. Refuting execution: the local from_iter drops everything, so the result does not contain 3.
//@ teeth-prior: Old gate listed std::collections::HashSet as a B path and matched def_path_str, which prints the local item identically. v3 measured: `fake` reaches ay and ay answers unknown (reason=incomplete: FSet model validation cannot produce a validated model), so FAILED is not reachable on FSet; the case therefore asserts only that ay was asked about `fake` and did NOT answer unsat — with the gate reverted `result@ == self@` plus into_iter's spec make the false contract unsat.
//@ teeth: v4 (wp-s38): the crate defines a module at a reserved library root, so the reserved-root backstop refuses the whole crate (exit 2) before any spec lookup; the lookalike can no longer reach ay, which the v3 teeth required. The DefId gate in collect_gate.rs stays covered by its unit tests (local lookalike identities classify None). Requires exactly that refusal, so an unrelated error cannot pass this case.
//@ verdict: error
//@ refused-with: local item `crate::std` shadows a standard or spec-library path root
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// B-side lookalike: LOCAL `std::collections::HashSet` whose from_iter drops everything.
pub mod std {
    pub mod collections {
        use creusot_std::prelude::*;
        pub struct HashSet<T>(pub ::std::collections::HashSet<T>);
        impl<T> View for HashSet<T> {
            type ViewTy = FSet<T>;
            #[logic(opaque)]
            fn view(self) -> FSet<T> { dead }
        }
        impl<T: ::std::hash::Hash + ::std::cmp::Eq> ::std::iter::FromIterator<T> for HashSet<T> {
            fn from_iter<I: ::std::iter::IntoIterator<Item = T>>(_it: I) -> Self {
                HashSet(::std::collections::HashSet::new())
            }
        }
    }
}

#[requires(s@.contains(3))]
#[ensures(result@.contains(3u32))]
pub fn fake(s: ::std::collections::HashSet<u32>) -> std::collections::HashSet<u32> {
    s.into_iter().collect()
}
