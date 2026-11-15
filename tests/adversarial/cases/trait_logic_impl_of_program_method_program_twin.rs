//@ expect: verify
//@ mechanism: the control for trait_logic_impl_of_program_method_granted: the same crate with W's
//@ mechanism: impl a PROGRAM `fn` returning true. The refusal is decided by the kind of item that
//@ mechanism: implements the program trait method, so a program body that discharges the inherited
//@ mechanism: `result` keeps `<W as Rd>::rd`, `gen_read` and `go`.
//@ fixed-by: D-110
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

pub struct W;

impl Rd for W {
    fn rd(&self) -> bool {
        true
    }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    W.rd()
}
