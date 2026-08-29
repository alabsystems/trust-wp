// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source span re-export from trust-wp-core.
//!
//! `SourceSpan` is the single canonical span type across all trust-wp crates.
//! It is defined in `trust_wp_core::formula` and re-exported here for
//! backward compatibility with existing `trust_wp_ay::SourceSpan` imports.
//!
//! See #655 for the consolidation rationale.

pub use trust_wp_core::formula::SourceSpan;
