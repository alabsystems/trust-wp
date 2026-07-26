// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: a logic trait method with an ordinary `where Self: Sized` bound —
//! the bound graph reaches `Sized`, which never cycles back, so the trait is
//! NOT illegal-recursive and the crate must keep compiling.

use trust_wp::logic;

pub trait Meas {
    #[logic]
    fn meas(&self) -> i32
    where
        Self: Sized;
}

impl Meas for i32 {
    #[logic]
    fn meas(&self) -> i32
    where
        Self: Sized,
    {
        5
    }
}

fn main() {}
