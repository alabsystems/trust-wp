// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! An impl that inherits its trait contract VERBATIM, so its refinement goal
//! is the tautology `P => P` and the BODY obligation is the only thing that
//! discharges the trait contract for a generic caller.
//!
//! With `TRUST_WP_PROBE_PANIC=<W as Rd>::rd` the body obligation is never
//! reached. The run must then refuse to hand `Rd::rd`'s contract to the
//! generic caller, rather than crediting a contract nothing proved.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

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
    gen_read::<W>(&W)
}

fn main() {}
