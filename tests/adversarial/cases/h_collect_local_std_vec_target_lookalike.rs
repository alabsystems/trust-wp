//@ expect: reject
//@ mechanism: collect roundtrip gate — (Self, B) identity must come from DefId provenance, never from a printed path
//@ fixed-by: wp-s24 (collect-hardening-v2, teeth v3)
//@ accept-means: the roundtrip was granted to a LOCAL lookalike std::vec::Vec target. Refuting execution: the local from_iter drops everything, so the result is empty, not length 2.
//@ teeth-prior: Old gate listed std::vec::Vec as a B path and matched def_path_str, which prints the local item as std::vec::Vec. v3 measured: `fake` reaches ay and ay answers unknown (quantifier-unhandled over the Seq ext_eq from into_iter's spec, with the lookalike view opaque), so the case asserts only that ay was asked about `fake` and did NOT answer unsat — with the gate reverted `result@ == self@` plus into_iter's spec make the false contract unsat.
//@ teeth: v4 (wp-s38): the crate defines a module at a reserved library root, so the reserved-root backstop refuses the whole crate (exit 2) before any spec lookup; the lookalike can no longer reach ay, which the v3 teeth required. The DefId gate in collect_gate.rs stays covered by its unit tests (local lookalike identities classify None). Requires exactly that refusal, so an unrelated error cannot pass this case.
//@ verdict: error
//@ refused-with: local item `crate::std` shadows a standard or spec-library path root
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// B-side lookalike: a LOCAL `std::vec::Vec` whose from_iter drops everything.
pub mod std {
    pub mod vec {
        use creusot_std::prelude::*;
        pub struct Vec<T>(pub ::std::vec::Vec<T>);
        impl<T> View for Vec<T> {
            type ViewTy = Seq<T>;
            #[logic(opaque)]
            fn view(self) -> Seq<T> { dead }
        }
        impl<T> ::std::iter::FromIterator<T> for Vec<T> {
            fn from_iter<I: ::std::iter::IntoIterator<Item = T>>(_it: I) -> Self {
                Vec(::std::vec::Vec::new())
            }
        }
    }
}

#[requires(v@.len() == 2)]
#[ensures(result@.len() == 2)]
pub fn fake(v: ::std::vec::Vec<u32>) -> std::vec::Vec<u32> {
    let r: std::vec::Vec<u32> = v.into_iter().collect();
    r
}
