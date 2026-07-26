// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

use trust_wp as _;

pub trait Tr {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn la();

    #[doc = "trust-wp:logic:"]
    fn lo();
}

impl Tr for () {
    #[doc = "trust-wp:logic:"]
    fn la() {}

    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn lo() {}
}

fn main() {}
