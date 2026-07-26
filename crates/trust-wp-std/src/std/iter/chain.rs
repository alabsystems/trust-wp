// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Chain<A, B>` iterator adapter helper surface.
//!
//! `Chain` wraps two iterators, yielding all elements from the first, then all
//! from the second. The wrapped iterator states are private, so these opaque
//! accessors give the driver rewrite stable names for the logical adapter state
//! while the Rust bodies stay specification-only placeholders.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Chain<A, B>`.
pub trait ChainExt<A: Iterator, B: Iterator> {
    /// Opaque access to the first iterator state.
    fn a(self) -> A;

    /// Opaque access to the second iterator state.
    fn b(self) -> B;
}

impl<A: Iterator, B: Iterator> ChainExt<A, B> for std::iter::Chain<A, B> {
    #[trusted]
    fn a(self) -> A {
        unreachable()
    }

    #[trusted]
    fn b(self) -> B {
        unreachable()
    }
}

impl<A: IteratorSpec, B: IteratorSpec<Item = A::Item>> IteratorSpec for std::iter::Chain<A, B> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
