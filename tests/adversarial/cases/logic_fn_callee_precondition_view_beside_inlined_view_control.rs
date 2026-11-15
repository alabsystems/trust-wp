//@ expect: verify
//@ xfail: the inlined `t.view()` is a call of the impl's `view` by its unique id, and the encoder has no definition registered for that id when the impl has no contract (`unsupported formula: logic function `__lfid__...view` is called but its definition is not registered`); the callee-precondition walk owes nothing here.
//@ mechanism: control for logic_fn_callee_precondition_view_beside_inlined_view, differing in the `View` impl's `#[requires]` alone: a view with no precondition owes nothing, and an inlined call whose arguments call nothing is no reason to refuse the body.
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

pub struct H;

impl H {
    #[logic(open)]
    pub fn helper(t: S) -> Int {
        t.view()
    }
}

#[logic]
#[requires(t.n > 0)]
#[ensures(true)]
pub fn caller(s: S, t: S) -> Int {
    pearlite! { s@ + H::helper(t) }
}
