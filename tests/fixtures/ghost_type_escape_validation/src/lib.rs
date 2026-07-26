// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

//! Ghost-type escape validation fixtures.
//!
//! These bins exercise the signature-only validation that rejects ordinary
//! program functions extracting values from `Ghost<T>` / `Snapshot<T>`
//! parameters while preserving the allow-listed ghost-context cases.

// The concrete cases live in the per-bin sources so each fixture compiles in
// isolation through trust-wp-rustc.
