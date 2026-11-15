//@ expect: reject
//@ mechanism: collect roundtrip gate — (Self, B) identity must come from DefId provenance, never from a printed path
//@ fixed-by: wp-s24 (collect-hardening-v2, teeth v3)
//@ accept-means: the roundtrip was granted to a LOCAL lookalike std::collections::hash_set::IntoIter. Refuting execution: the local next() returns None, so the collected set is empty and does not contain 3.
//@ teeth-prior: Old gate listed std::collections::hash_set::IntoIter as a Self path and matched def_path_str, which prints the local item identically. v3 measured: `fake` reaches ay (the constructor fn `new` alone is refused by the compound single-field guard) and ay answers unknown (reason=incomplete: FSet model validation cannot produce a validated model), so FAILED is not reachable on FSet; the case therefore asserts only that ay was asked about `fake` and did NOT answer unsat — with the gate reverted `result@ == self@` plus `new`'s ensures make the false contract unsat.
//@ teeth: v4 (wp-s38): the crate defines a module at a reserved library root, so the reserved-root backstop refuses the whole crate (exit 2) before any spec lookup; the lookalike can no longer reach ay, which the v3 teeth required. The DefId gate in collect_gate.rs stays covered by its unit tests (local lookalike identities classify None). Requires exactly that refusal, so an unrelated error cannot pass this case.
//@ verdict: error
//@ refused-with: local item `crate::std` shadows a standard or spec-library path root
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// Self-side lookalike: LOCAL `std::collections::hash_set::IntoIter` that
// produces nothing, collected into the REAL HashSet.
pub mod std {
    pub mod collections {
        pub mod hash_set {
            use creusot_std::prelude::*;
            pub struct IntoIter<T>(pub ::std::collections::HashSet<T>);
            impl<T: DeepModel> IntoIter<T> {
                #[ensures(result@ == s@)]
                pub fn new(s: ::std::collections::HashSet<T>) -> Self {
                    IntoIter(s)
                }
            }
            impl<T: DeepModel> View for IntoIter<T> {
                type ViewTy = FSet<T::DeepModelTy>;
                #[logic(open)]
                fn view(self) -> FSet<T::DeepModelTy> { pearlite! { self.0@ } }
            }
            impl<T> ::std::iter::Iterator for IntoIter<T> {
                type Item = T;
                fn next(&mut self) -> ::std::option::Option<T> { ::std::option::Option::None }
            }
        }
    }
}

#[requires(s@.contains(3))]
#[ensures(result@.contains(3))]
pub fn fake(s: ::std::collections::HashSet<u32>) -> ::std::collections::HashSet<u32> {
    let it = std::collections::hash_set::IntoIter::new(s);
    it.collect()
}
