// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Filter<I, P>` iterator adapter helper surface.
//!
//! `Filter` wraps an iterator and a predicate, yielding only elements for
//! which the predicate returns `true`. Both the wrapped iterator and predicate
//! are private, so these opaque accessors give the driver rewrite stable names
//! for the logical adapter state while the Rust bodies stay specification-only
//! placeholders.
//!
//! Reference: `creusot-std/src/std/iter/filter.rs`

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Filter<I, P>`.
#[allow(clippy::iter_not_returning_iterator)] // Creusot-compatible spec surface
pub trait FilterExt<I, P> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;

    /// Opaque access to the filter predicate.
    fn func(self) -> P;
}

impl<I, P> FilterExt<I, P> for std::iter::Filter<I, P> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }

    #[trusted]
    fn func(self) -> P {
        unreachable()
    }
}

impl<I, P> IteratorSpec for std::iter::Filter<I, P>
where
    I: IteratorSpec,
    P: for<'a> FnMut(&'a I::Item) -> bool,
{
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
