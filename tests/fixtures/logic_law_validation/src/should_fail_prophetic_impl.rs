// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

use trust_wp as _;

pub trait Tr {
    #[doc = "trust-wp:logic:"]
    fn f();
}

impl Tr for () {
    #[doc = "trust-wp:logic:prophetic:"]
    fn f() {}
}

fn main() {}
