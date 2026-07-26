// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Skip<I>` iterator adapter helper surface.
//!
//! `Skip` hides both its wrapped iterator state and its remaining skip counter.
//! These opaque accessors give the driver rewrite stable names for the logical
//! adapter state while the Rust bodies stay specification-only placeholders.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Skip<I>`.
pub trait SkipExt<I: Iterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;

    /// Opaque access to the remaining skip count.
    fn n(self) -> usize;
}

impl<I: Iterator> SkipExt<I> for std::iter::Skip<I> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }

    #[trusted]
    fn n(self) -> usize {
        unreachable()
    }
}

impl<I: IteratorSpec> IteratorSpec for std::iter::Skip<I> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
