// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S;

impl Clone for S {
    #[requires(false)]
    fn clone(&self) -> S {
        S
    }
}

fn main() {}
