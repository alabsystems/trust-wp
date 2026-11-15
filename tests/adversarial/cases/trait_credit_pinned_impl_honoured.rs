//@ expect: reject
//@ mechanism: the true twin of trait_credit_pinned_impl_refuted: `<V as Rd>::rd` returns true and
//@ mechanism: honours `Rd::rd`, while `<W as Rd>::rd` still refutes it. A call pinned to V's impl
//@ mechanism: rests on V's impl alone, so `go_vd`, `V::m` and `go_vm` keep their credits; every
//@ mechanism: call that may run W's impl is withdrawn: `go_wd` (pinned to it), `gen_read` and
//@ mechanism: `go_dyn` (any impl), `go_v` (through `gen_read`), and `go_wrap_v` (pinned to a
//@ mechanism: generic impl whose body calls `Rd::rd` at `T`, which the walk does not instantiate).
//@ fixed-by: D-94 (a trait-method call pinned to one local impl item rests on that item)
//@ accept-means: `go_wd` claims `result` and returns false; `gen_read` claims it for every `T: Rd`; `go_dyn` claims it through a `dyn Rd` holding W.
//@ teeth: the run rejects because W's impl fails. Under D-86 `go_vd`, `V::m` and `go_vm` were withdrawn here too, although true (the price D-94 narrows). `go_v` and `go_wrap_v` are true and stay withdrawn: that is the price D-94 keeps.
//@ note: `go_dyn` is refused before the walk today (a `dyn` call is not modelled); once it is credited, the walk must not pin it.
//@ note: `go_vf` reaches V's impl through a fn-item local (`let f = <V as Rd>::rd; f(&V)`). The credit graph pins that name to V's impl, but the call-site ledger backtracks the local to the trait method, so the grant names `Rd::rd` and `go_vf` stays withdrawn although true: a price D-110 records against D-94.
//@ also-verified: go_vd, V::m, go_vm, go_v, go_wrap_v, go_vf, <V as Rd>::rd, <Wrap<T> as Rd>::rd
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
        true
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

#[ensures(result)]
pub fn go_vf() -> bool {
    let f = <V as Rd>::rd;
    f(&V)
}
