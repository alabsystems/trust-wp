// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Iterator support for `Seq<T>`: `SeqIter`, `IntoIterator`, and
//! `IteratorSpec` implementations.

use super::Seq;
use crate::logic::Int;

/// Owning iterator over a `Seq<T>`.
///
/// Produced by `Seq::into_iter()`. Drains elements front-to-back.
///
/// Reference: Creusot `creusot-std/src/logic/seq.rs` `SeqIter`.
pub struct SeqIter<T> {
    inner: Seq<T>,
}

impl<T> IntoIterator for Seq<T> {
    type Item = T;
    type IntoIter = SeqIter<T>;

    fn into_iter(self) -> SeqIter<T> {
        SeqIter { inner: self }
    }
}

impl<'a, T> IntoIterator for &'a Seq<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.iter()
    }
}

impl<T> Iterator for SeqIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.inner.elements.is_empty() {
            None
        } else {
            Some(self.inner.elements.remove(0))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.inner.elements.len();
        (len, Some(len))
    }
}

impl<T> crate::std::iter::IteratorSpec for SeqIter<T> {
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        Int::from(self.inner.elements.len()) == visited.len() + Int::from(o.inner.elements.len())
    }

    fn completed(&mut self) -> bool {
        self.inner.elements.is_empty()
    }
}
