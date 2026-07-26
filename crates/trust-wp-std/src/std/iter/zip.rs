// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Zip<A, B>` iterator adapter helper surface.
//!
//! The wrapped iterator states are private, so these opaque accessors give the
//! driver rewrite stable names for the logical adapter state while the Rust
//! bodies stay specification-only placeholders.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Zip<A, B>`.
pub trait ZipExt<A: Iterator, B: Iterator> {
    /// Opaque access to the left iterator state.
    fn itera(self) -> A;

    /// Opaque access to the right iterator state.
    fn iterb(self) -> B;
}

impl<A: Iterator, B: Iterator> ZipExt<A, B> for std::iter::Zip<A, B> {
    #[trusted]
    fn itera(self) -> A {
        unreachable()
    }

    #[trusted]
    fn iterb(self) -> B {
        unreachable()
    }
}

impl<A: IteratorSpec, B: IteratorSpec> IteratorSpec for std::iter::Zip<A, B> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
