// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twin of should_fail_sum: counting instead of summing.

use trust_wp::ensures;

#[ensures(true)]
pub fn len_twin(v: &[u8]) -> usize {
    v.len() / 2
}

fn main() {}
