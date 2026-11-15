//@ expect: reject
//@ mechanism: a std container's drop glue drops its elements: Vec<Dropper> whose contract-free Drop::drop panics
//@ fixed-by: s44 (wp-s44, contracted panic sites) — std types are walked through their type arguments only
//@ accept-means: `vec_drop` verified although dropping the vector runs Dropper::drop, which panics.
//@ teeth: must stay rejected once std private fields (hashbrown tables) are no longer walked.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct Dropper(pub u8);

impl Drop for Dropper {
    fn drop(&mut self) {
        panic!("dropped")
    }
}

#[ensures(true)]
pub fn vec_drop(v: Vec<Dropper>) {
    let _w = v;
}
