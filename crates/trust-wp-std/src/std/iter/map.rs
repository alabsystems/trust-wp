// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Map<I, F>` iterator adapter helper surface.
//!
//! `Map` wraps an iterator and a closure, applying the closure to each element.
//! The wrapped iterator and closure are private, so these opaque accessors give
//! the driver rewrite stable names for the logical adapter state while the Rust
//! bodies stay specification-only placeholders.
//!
//! Reference: `creusot-std/src/std/iter/map.rs`

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Map<I, F>`.
#[allow(clippy::iter_not_returning_iterator)] // Creusot-compatible spec surface
pub trait MapExt<I, F> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;

    /// Opaque access to the mapping closure.
    fn func(self) -> F;
}

impl<I, F> MapExt<I, F> for std::iter::Map<I, F> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }

    #[trusted]
    fn func(self) -> F {
        unreachable()
    }
}

impl<I: IteratorSpec, B, F: FnMut(I::Item) -> B> IteratorSpec for std::iter::Map<I, F> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
