// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RAII guards for encoding traversal state.
//!
//! `DepthGuard` and `PathConditionGuard` ensure the encoder's recursion depth
//! counter and path-condition stack stay balanced even on early returns or panics.
//! Extracted from `encoder/mod.rs` (#2655).

use ay_dpll::api::Term;

/// RAII guard that decrements a depth counter on drop.
///
/// Used by `encode` and `encode_pure_impl` to ensure `recursion_depth` is
/// decremented on all exit paths — including `?` and early `return` — without
/// adding an extra stack frame. (#1116)
///
/// DESIGN: Raw pointer (`*mut usize`) is intentional. A `&mut usize` borrow
/// would conflict with `&mut self` in recursive `encode()` calls. `Cell<usize>`
/// would avoid unsafe but forces non-`&mut self` signatures throughout the
/// encoder. The raw pointer pattern is narrow, well-documented, and standard
/// for self-referential RAII guards in Rust. (#1411)
pub(super) struct DepthGuard(pub(super) *mut usize);

impl Drop for DepthGuard {
    fn drop(&mut self) {
        // SAFETY: The pointer targets `AYEncoder::recursion_depth` which is
        // owned by the encoder. The guard's lifetime is limited to the
        // encoding function that created it, and the encoder is borrowed
        // mutably for the entire call, so no aliasing occurs.
        unsafe { *self.0 -= 1 };
    }
}

/// RAII guard that pops one element from `path_conditions` on drop.
///
/// Ensures the path-condition stack stays balanced even if `encode_pure_impl`
/// panics inside an `Ite` branch. (#1207, #1584)
pub(in crate::encoder) struct PathConditionGuard(pub(in crate::encoder) *mut Vec<Term>);

impl Drop for PathConditionGuard {
    fn drop(&mut self) {
        // SAFETY: The pointer targets `AYEncoder::path_conditions` which is
        // owned by the encoder. The guard's lifetime is limited to the Ite
        // branch scope, and the encoder is borrowed mutably for the entire
        // call, so no aliasing occurs.
        unsafe { (*self.0).pop() };
    }
}
