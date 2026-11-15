//@ expect: verify
//@ xfail: the crate implements `Tr` for `u8`, so a clause spelling `Self` as a type is refused
//@ xfail: anywhere in it (D-205): the parser cannot tell which impl a clause is restated at.
//@ xfail: Before D-205 the binder was read unbounded and the true contract refuted.
//@ mechanism: control: every `u8` is below 256, and the impl for `u8` of `Tr::m`, which inherits
//@ mechanism: `result == (forall<x: Self> x@ < 256)`, returns true. The isolating twin of
//@ mechanism: trait_contract_self_binder_inherited_by_machine_int_impl_granted.rs.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `<u8 as Tr>::m FAILED ✗` before D-205, refused
//@ teeth: with it)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr: View<ViewTy = Int> + Sized {
    #[ensures(result == (forall<x: Self> x@ < 256))]
    fn m() -> bool;
}

impl Tr for u8 {
    fn m() -> bool {
        true
    }
}
