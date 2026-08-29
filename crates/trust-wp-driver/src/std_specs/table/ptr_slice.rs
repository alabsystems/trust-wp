// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Char, raw pointer, and slice specs — imported from `trust-wp-std` shared registry.
//!
//! Path ownership migrated to `trust_wp_std::std::lookup_registry` (#2524).
//! This module re-exports the shared registry slice for the driver's
//! `STD_SPEC_TABLES`.

use super::super::SpecEntry;

pub(super) static SPECS: &[SpecEntry] = trust_wp_std::std::lookup_registry::PTR_SLICE;
