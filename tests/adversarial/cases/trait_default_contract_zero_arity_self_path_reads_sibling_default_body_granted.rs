//@ expect: reject
//@ mechanism: the zero-argument spelling of trait_default_contract_self_path_reads_sibling_default_body_granted.rs:
//@ mechanism: `Foo::get`'s default claims `result@ == Self::h()` and returns 0, where `h`'s visible default
//@ mechanism: is 0 and `()`'s impl overrides it (5). `resolve_call_name` withholds the declaration
//@ mechanism: `Foo::h` (visible default body) by answering "unresolved", the call stays `Self::h`, and the
//@ mechanism: encoder reads the declaration's default body at the abstract `Self`. No receiver is involved.
//@ fixed-by: OPEN — committed RED rather than hidden; the same defect as
//@ fixed-by: trait_default_contract_self_path_reads_sibling_default_body_granted.rs.
//@ accept-means: `caller` is credited with `result@ == 5` for `().get()`, which returns 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`Foo::get verified ✓`, `caller verified ✓`) with the block-scope
//@ teeth: resolver (D-195..D-209) and at the campaign tip it was built on alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic(open)]
    fn h() -> Int {
        pearlite! { 0 }
    }

    // WRONG for an impl that overrides `h`.
    #[ensures(result@ == Self::h())]
    fn get(&self) -> i32 {
        0
    }
}

impl Foo for () {
    #[logic(open)]
    fn h() -> Int {
        pearlite! { 5 }
    }
}

// WRONG: `().get()` is the default (0).
#[ensures(result@ == 5)]
pub fn caller() -> i32 {
    ().get()
}
