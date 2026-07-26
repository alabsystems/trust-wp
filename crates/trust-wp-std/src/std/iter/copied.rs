// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Copied<I>` iterator adapter helper surface.
//!
//! Like `Cloned`, this adapter needs an opaque `iter()` accessor for driver-side
//! lowering because the wrapped iterator is not publicly accessible.

use super::IteratorSpec;
use crate::{
    logic::{unreachable, Seq},
    trusted,
};

/// Specification-only accessor surface for `Copied<I>`.
pub trait CopiedExt<I: Iterator> {
    /// Opaque access to the wrapped iterator state.
    fn iter(self) -> I;
}

impl<I> CopiedExt<I> for std::iter::Copied<I>
where
    I: Iterator,
{
    #[trusted]
    fn iter(self) -> I {
        unreachable()
    }
}

impl<'a, I, T: 'a> IteratorSpec for std::iter::Copied<I>
where
    I: IteratorSpec<Item = &'a T>,
    T: Copy,
{
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        let _ = (visited, o);
        unreachable()
    }

    fn completed(&mut self) -> bool {
        unreachable()
    }
}
