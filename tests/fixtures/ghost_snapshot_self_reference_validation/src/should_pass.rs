// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Snapshot self-reference fixtures that should PASS.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct GoodSnapshot<'a> {
    snap: Snapshot<&'a mut u32>,
}

pub struct GoodShared<'a> {
    snap: Snapshot<&'a GoodShared<'a>>,
}

pub struct GoodGhost<'a> {
    ghost: Ghost<&'a mut GoodGhost<'a>>,
}

fn main() {}
