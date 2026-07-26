// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Cloned<I>` iterator adapter helper surface.
//!
//! The wrapped iterator state is private, so the accessor and `IteratorSpec`
//! bodies are specification-only placeholders that the driver rewrite refines.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Cloned<I>`.
pub trait ClonedExt<I: Iterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;
}

impl<I> ClonedExt<I> for std::iter::Cloned<I>
where
    I: Iterator,
{
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }
}

impl<'a, I, T: 'a> IteratorSpec for std::iter::Cloned<I>
where
    I: IteratorSpec<Item = &'a T>,
    T: Clone,
{
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
