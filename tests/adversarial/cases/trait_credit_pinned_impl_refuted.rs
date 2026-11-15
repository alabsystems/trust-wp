//@ expect: reject
//@ mechanism: a call the resolver pins to one impl item rests on that impl alone, so the
//@ mechanism: withdrawal must still reach it when THAT impl refutes the contract. Both impls of
//@ mechanism: `Rd::rd` inherit `result` and return false. `go_vd` calls `V.rd()` and `V::m`
//@ mechanism: calls `self.rd()`, both pinned to `<V as Rd>::rd`; `go_vm` is one call away through
//@ mechanism: `V::m`; `go_wd` is pinned to `<W as Rd>::rd`; `gen_read` and `go_dyn` may run any
//@ mechanism: impl; `go_wrap_v` is pinned to a generic impl whose body calls `Rd::rd` at `T`.
//@ fixed-by: D-94 (a trait-method call pinned to one local impl item rests on that item)
//@ accept-means: any of `go_vd`, `V::m`, `go_vm`, `go_wd`, `go_v`, `go_dyn`, `go_wrap_v` claims `result` and returns false; `gen_read` claims it for every `T: Rd`.
//@ note: `go_dyn` is refused before the walk today (a `dyn` call is not modelled); once it is credited, the walk must not pin it.
//@ teeth: the isolating twin trait_credit_pinned_impl_honoured.rs differs in one token (`<V as Rd>::rd` returns true) and keeps `go_vd`, `V::m`, `go_vm` credited, so a pin that ignored the impl it names would fail here.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;
pub struct V;
pub struct Wrap<T>(pub T);

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

impl Rd for W {
    fn rd(&self) -> bool {
        false
    }
}

impl Rd for V {
    fn rd(&self) -> bool {
        false
    }
}

impl<T: Rd> Rd for Wrap<T> {
    fn rd(&self) -> bool {
        self.0.rd()
    }
}

impl V {
    #[ensures(result)]
    pub fn m(&self) -> bool {
        self.rd()
    }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go_v() -> bool {
    gen_read::<V>(&V)
}

#[ensures(result)]
pub fn go_vd() -> bool {
    V.rd()
}

#[ensures(result)]
pub fn go_vm() -> bool {
    V.m()
}

#[ensures(result)]
pub fn go_wd() -> bool {
    W.rd()
}

#[ensures(result)]
pub fn go_dyn() -> bool {
    let r: &dyn Rd = &W;
    r.rd()
}

#[ensures(result)]
pub fn go_wrap_v() -> bool {
    Wrap(V).rd()
}
