// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

use trust_wp_std::erasure;

pub fn bar() -> i32 {
    baz::<42>()
}

pub fn baz<const N: i32>() -> i32 {
    N
}

#[erasure(baz::<N>)]
pub fn baz2<const N: i32>() -> i32 {
    N
}

#[erasure(bar)]
pub fn bar2() -> i32 {
    baz::<0>()
}

#[erasure(bar)]
pub fn bar3() -> i32 {
    baz2::<0>()
}

pub fn add(x: usize, y: usize) -> usize {
    x + y
}

#[erasure(add)]
pub fn add2(x: usize, _y: usize) -> usize {
    x + x
}

pub trait Quux {
    fn quux();
}

#[erasure(T::quux)]
pub fn quux2<T: Quux>() {}

fn main() {}
