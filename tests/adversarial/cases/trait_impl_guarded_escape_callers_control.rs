//@ expect: verify
//@ mechanism: control for trait_impl_escape_withdrawal_leaves_trait_callers_credited: the impl
//@ mechanism: hands `Option::map` a closure whose index is guarded, so the closure verifies, the
//@ mechanism: impl keeps its credit and so do the callers resting on `Tr::m`.
//@ accept-means: n/a (control)
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32 {
        let _ = o.map(|j| if j < w.len() { w[j] } else { 0 });
        1
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w)
}

#[ensures(result@ == 1)]
pub fn conc(o: Option<usize>, w: &[u32]) -> u32 {
    S.m(o, w)
}
