// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Take<I>` iterator adapter helper surface.
//!
//! `Take` hides both its wrapped iterator state and its remaining-element
//! counter. These opaque accessors give the driver rewrite stable names for the
//! logical adapter state while the Rust bodies stay specification-only
//! placeholders.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Take<I>`.
pub trait TakeExt<I: Iterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;

    /// Opaque access to the mutable wrapped iterator state.
    fn iter_mut(&mut self) -> &mut I;

    /// Opaque access to the remaining step bound.
    fn n(self) -> usize;
}

impl<I: Iterator> TakeExt<I> for std::iter::Take<I> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }

    #[trusted]
    fn iter_mut(&mut self) -> &mut I {
        unreachable()
    }

    #[trusted]
    fn n(self) -> usize {
        unreachable()
    }
}

impl<I: IteratorSpec> IteratorSpec for std::iter::Take<I> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
