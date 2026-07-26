// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Rev<I>` iterator adapter helper surface.
//!
//! `Rev` wraps a `DoubleEndedIterator` and yields elements in reverse order
//! by delegating forward `produces` to the inner `produces_back`. The `iter()`
//! accessor gives the driver rewrite a stable name for the wrapped iterator.

use super::{DoubleEndedIteratorSpec, IteratorSpec};
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Rev<I>`.
pub trait RevExt<I: DoubleEndedIterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;
}

impl<I: DoubleEndedIterator> RevExt<I> for std::iter::Rev<I> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }
}

impl<I: DoubleEndedIteratorSpec> IteratorSpec for std::iter::Rev<I> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        self.iter().produces_back(visited, o.iter())
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
