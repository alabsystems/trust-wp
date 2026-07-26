// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for cargo-trust-wp against fixture projects.
//!
//! This file is a thin module loader. All test bodies and the shared harness
//! live under `e2e/`. Existing `cargo test -p cargo-trust-wp --test e2e ...`
//! usage remains valid.

#[path = "e2e/support.rs"]
mod support;

#[path = "e2e/smoke.rs"]
mod smoke;

#[path = "e2e/simple_examples.rs"]
mod simple_examples;

#[path = "e2e/extern_spec.rs"]
mod extern_spec;

#[path = "e2e/traits.rs"]
mod traits;

#[path = "e2e/closures/mod.rs"]
mod closures;

#[path = "e2e/loops.rs"]
mod loops;

#[path = "e2e/termination.rs"]
mod termination;
