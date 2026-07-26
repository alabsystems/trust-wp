// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Fuse<I>` iterator adapter helper surface.
//!
//! `Fuse` does not expose its wrapped iterator publicly. These methods exist so
//! the driver rewrite can target stable accessor names in specs.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Fuse<I>`.
pub trait FuseExt<I: Iterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;
}

impl<I: Iterator> FuseExt<I> for std::iter::Fuse<I> {
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }
}

impl<I: IteratorSpec> IteratorSpec for std::iter::Fuse<I> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
