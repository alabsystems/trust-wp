// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Snapshot self-reference fixtures that should FAIL.
//!
//! These mirror the driver-side gap behind `tests/should_fail/bug/436_2.rs`:
//! recursive `Snapshot<&mut T>` shapes must be rejected before verification.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct BadDirect<'a> {
    snap: Snapshot<&'a mut BadDirect<'a>>,
}

pub struct BadOption<'a> {
    snap: Snapshot<&'a mut Option<BadOption<'a>>>,
}

pub enum BadEnum<'a> {
    None,
    Some(Snapshot<&'a mut BadEnum<'a>>),
}

fn main() {}
