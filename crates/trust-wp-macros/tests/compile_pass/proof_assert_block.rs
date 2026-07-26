// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

use trust_wp_macros::proof_assert;

fn lemma_call() {}

fn proof_assert_block_form_compiles() {
    proof_assert! {
        lemma_call();
        1i32 == 1i32
    };
}

fn main() {}
