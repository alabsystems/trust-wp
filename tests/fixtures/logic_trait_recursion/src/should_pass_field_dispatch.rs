// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN: an impl logic method calling the SAME-NAMED trait method on a
//! FIELD (`self.inner.size()`), the structural-descent pattern behind View /
//! DeepModel impls. The receiver is not `self`, so the self-named
//! self-dispatch threading must NOT fire — this must keep compiling.

use trust_wp::logic;

pub trait Size {
    #[logic]
    fn size(&self) -> i32;
}

pub struct Inner;

impl Size for Inner {
    #[logic]
    fn size(&self) -> i32 {
        1
    }
}

pub struct Outer {
    pub inner: Inner,
}

impl Size for Outer {
    #[logic]
    fn size(&self) -> i32 {
        self.inner.size()
    }
}

fn main() {}
