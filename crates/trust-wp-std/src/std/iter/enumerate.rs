// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Enumerate<I>` iterator adapter helper surface.
//!
//! The wrapped iterator state and running offset are private, so these opaque
//! accessors give the driver rewrite stable names for the logical adapter
//! state while the Rust bodies stay specification-only placeholders.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Enumerate<I>`.
pub trait EnumerateExt<I: Iterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;

    /// Opaque access to the current offset.
    fn n(self) -> usize;
}

impl<I: Iterator> EnumerateExt<I> for std::iter::Enumerate<I> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }

    #[trusted]
    fn n(self) -> usize {
        unreachable()
    }
}

impl<I: IteratorSpec> IteratorSpec for std::iter::Enumerate<I> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
