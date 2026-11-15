//@ expect: reject
//@ mechanism: collect roundtrip gate — (Self, B) identity must come from DefId provenance, never from a printed path
//@ fixed-by: wp-s24 (collect-hardening-v2, teeth v3)
//@ accept-means: the roundtrip result@ == self@ was granted to a LOCAL lookalike of alloc::vec::IntoIter (def_path_str omits the local crate). Refuting execution: the local next() returns None, so the collected Vec is empty, not length 2.
//@ teeth-prior: Review of 51cca4a: exit 0, verified, with debug self=[creusot_test::alloc::vec::IntoIter, alloc::vec::IntoIter] -> Some(VecIntoIter). v3: the lookalike is built through a constructor fn (a tuple-struct aggregate in `fake` was refused by the compound single-field guard before the solver ran), so `fake` reaches ay; the case requires FAILED with ay not unsat — with the gate reverted the roundtrip plus `new`'s ensures make the false contract unsat.
//@ teeth: v4 (wp-s38): the crate defines a module at a reserved library root, so the reserved-root backstop refuses the whole crate (exit 2) before any spec lookup; the lookalike can no longer reach ay, which the v3 teeth required. The DefId gate in collect_gate.rs stays covered by its unit tests (local lookalike identities classify None). Requires exactly that refusal, so an unrelated error cannot pass this case.
//@ verdict: error
//@ refused-with: local item `crate::alloc` shadows a standard or spec-library path root
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// A LOCAL module whose def_path_str is `alloc::vec::IntoIter`.
pub mod alloc {
    pub mod vec {
        use creusot_std::prelude::*;
        pub struct IntoIter<T>(pub Vec<T>);
        impl<T> IntoIter<T> {
            #[ensures(result@ == v@)]
            pub fn new(v: Vec<T>) -> Self {
                IntoIter(v)
            }
        }
        impl<T> View for IntoIter<T> {
            type ViewTy = Seq<T>;
            #[logic(open)]
            fn view(self) -> Seq<T> { pearlite! { self.0@ } }
        }
        impl<T> Iterator for IntoIter<T> {
            type Item = T;
            fn next(&mut self) -> Option<T> { None }
        }
    }
}

#[requires(v@.len() == 2)]
#[ensures(result@.len() == 2)]
pub fn fake(v: Vec<u32>) -> Vec<u32> {
    let it = alloc::vec::IntoIter::new(v);
    let r: Vec<u32> = it.collect();
    r
}
