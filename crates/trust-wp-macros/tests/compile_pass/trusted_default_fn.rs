// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `#[trusted]` accepts a specialization `default fn`
//! (`syn::ImplItemFn` with `defaultness`). Stripping `default` would trip
//! E0520, so the marker must preserve it.

#![feature(min_specialization)]

use trust_wp_macros::{ensures, trusted};

trait T {
    fn x(self);
}

impl<U> T for Vec<U> {
    #[trusted]
    #[ensures(true)]
    default fn x(self) {}
}

impl T for Vec<u32> {
    #[trusted]
    #[ensures(true)]
    fn x(self) {}
}

fn main() {
    let v: Vec<u32> = Vec::new();
    v.x();
}
