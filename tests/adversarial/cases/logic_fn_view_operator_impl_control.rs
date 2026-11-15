//@ expect: verify
//@ mechanism: control for logic_fn_view_operator_impl_precondition, differing in the `View` impl's `#[requires]` alone: an impl with no precondition owes nothing, so a fix that finds the impl behind `s@` must still verify the caller.
//@ accept-means: n/a (control) — the view that runs has no precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub n: Int,
}

impl View for S {
    type ViewTy = Int;

    #[logic]
    fn view(self) -> Int {
        pearlite! { self.n }
    }
}

#[logic]
#[ensures(true)]
pub fn caller(s: S) -> Int {
    pearlite! { s@ }
}
