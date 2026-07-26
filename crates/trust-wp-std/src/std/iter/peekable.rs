// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Peekable<I>` iterator adapter helper surface.
//!
//! `Peekable` wraps an iterator and allows peeking at the next element
//! without consuming it. The wrapped iterator state is private, so this
//! opaque accessor gives the driver rewrite a stable name for the logical
//! adapter state while the Rust body stays a specification-only placeholder.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Peekable<I>`.
pub trait PeekableExt<I: Iterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;
}

impl<I: Iterator> PeekableExt<I> for std::iter::Peekable<I> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }
}

impl<I: IteratorSpec> IteratorSpec for std::iter::Peekable<I> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
