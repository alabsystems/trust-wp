// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shell boundary layer for `AYEncoder`.
//!
//! This module contains forwarding methods on `AYEncoder` that delegate
//! to already-extracted state owners (`DeclarationState`, `SortResolverState`,
//! `QuantifierState`, `SeqState`, `AdtState`, `AssertionPipelineState`).
//!
//! The shell keeps `encoder/mod.rs` focused on struct definition, constants,
//! RAII guards, and actual encoding entrypoints.
//!
//! See: `designs/2026-03-20-2588-encoder-shell-submodules.md`
//! Issue: #2588

mod declarations;
mod path;
mod seq_propagation;
mod sort_resolver;
mod state_access;
