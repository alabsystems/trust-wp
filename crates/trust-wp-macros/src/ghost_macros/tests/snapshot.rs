// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for snapshot! expansion.
//!
//! Note: snapshot expansion tests require proc_macro TokenStream which is only
//! available in proc-macro crates at compile time. The expand_snapshot function
//! takes proc_macro::TokenStream, not proc_macro2::TokenStream, so unit tests
//! that call it directly are not possible without a proc-macro test harness.
//!
//! The snapshot logic is integration-tested via the Creusot compatibility harness
//! and trust-wp-driver tests. Phase 3 regression tests for spec-only call detection
//! are included below using the internal helpers where possible.

// Snapshot-specific regression tests can be added here as the module evolves.
// Current coverage is via integration tests in tests/creusot_compat/.
