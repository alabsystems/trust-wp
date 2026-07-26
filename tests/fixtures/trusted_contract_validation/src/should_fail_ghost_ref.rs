// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[check(ghost)]
pub fn faux() -> bool {
    true
}

#[trusted]
#[requires(faux())]
pub fn trusted_bad() {}

fn main() {}
