// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `#[trusted]` accepts `proof_assert!` macro invocation.
//!
//! Creusot uses `#[trusted] proof_assert! { ... }` inside function bodies to
//! represent trusted assertions (e.g., `syntax/05_annotations.rs`).
//!
//! Requires nightly features: `proc_macro_hygiene` allows attribute macros on
//! statements, and `stmt_expr_attributes` allows attributes on expressions.
//! The trust-wp-driver and harness inject these automatically.

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]
#![allow(unexpected_cfgs)]

use trust_wp_macros::{ensures, trusted};

#[ensures(b)]
#[allow(unused_variables)]
pub fn assume(b: bool) {
    #[trusted]
    trust_wp_macros::proof_assert! { b };
}

fn main() {
    assume(true);
}
