// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trait and conversion implementations for `Seq<T>`.

use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

use super::Seq;
use crate::logic::{ops::IndexLogic, Int};

impl<T: Clone> Clone for Seq<T> {
    fn clone(&self) -> Self {
        Self {
            elements: self.elements.clone(),
        }
    }
}

impl<T: PartialEq> PartialEq for Seq<T> {
    fn eq(&self, other: &Self) -> bool {
        self.elements == other.elements
    }
}

impl<T: Eq> Eq for Seq<T> {}

impl<T> Default for Seq<T> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<T> From<Vec<T>> for Seq<T> {
    fn from(elements: Vec<T>) -> Self {
        Self { elements }
    }
}

impl<T> From<Seq<T>> for Vec<T> {
    fn from(seq: Seq<T>) -> Self {
        seq.elements
    }
}

// Index implementations for `seq[i]` syntax.

impl<T> std::ops::Index<usize> for Seq<T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        &self.elements[index]
    }
}

impl<T> std::ops::Index<Int> for Seq<T> {
    type Output = T;
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    fn index(&self, index: Int) -> &T {
        &self.elements[index.0 as usize]
    }
}

impl<T> std::ops::Index<i32> for Seq<T> {
    type Output = T;
    #[allow(clippy::cast_sign_loss)]
    fn index(&self, index: i32) -> &T {
        &self.elements[index as usize]
    }
}

// IndexLogic implementations for specification-level indexing.
// These match Creusot's `IndexLogic` trait impls on `Seq<T>`.
// Reference: `creusot-std/src/logic/seq.rs:441-503`

impl<T: Clone> IndexLogic<Int> for Seq<T> {
    type Item = T;

    fn index_logic(self, idx: Int) -> Self::Item {
        let i = idx.0 as usize;
        self.elements[i].clone()
    }
}

impl<T: Clone> IndexLogic<Range<Int>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: Range<Int>) -> Self::Item {
        self.subsequence(range.start, range.end)
    }
}

impl<T: Clone> IndexLogic<RangeInclusive<Int>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: RangeInclusive<Int>) -> Self::Item {
        let start = *range.start();
        let end = *range.end();
        self.subsequence(start, end + 1)
    }
}

impl<T: Clone> IndexLogic<RangeFull> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, _: RangeFull) -> Self::Item {
        self
    }
}

impl<T: Clone> IndexLogic<RangeFrom<Int>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: RangeFrom<Int>) -> Self::Item {
        let len = self.len();
        self.subsequence(range.start, len)
    }
}

impl<T: Clone> IndexLogic<RangeTo<Int>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: RangeTo<Int>) -> Self::Item {
        self.subsequence(Int(0), range.end)
    }
}

impl<T: Clone> IndexLogic<RangeToInclusive<Int>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: RangeToInclusive<Int>) -> Self::Item {
        self.subsequence(Int(0), range.end + 1)
    }
}

// IndexLogic implementations for usize ranges (convenience for integer literals).

impl<T: Clone> IndexLogic<Range<usize>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: Range<usize>) -> Self::Item {
        self.subsequence(Int(range.start as i128), Int(range.end as i128))
    }
}

impl<T: Clone> IndexLogic<RangeFrom<usize>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: RangeFrom<usize>) -> Self::Item {
        let len = self.len();
        self.subsequence(Int(range.start as i128), len)
    }
}

impl<T: Clone> IndexLogic<RangeTo<usize>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: RangeTo<usize>) -> Self::Item {
        self.subsequence(Int(0), Int(range.end as i128))
    }
}

impl<T: Clone> IndexLogic<RangeInclusive<usize>> for Seq<T> {
    type Item = Seq<T>;

    #[allow(clippy::range_plus_one)]
    fn index_logic(self, range: RangeInclusive<usize>) -> Self::Item {
        let start = *range.start();
        let end = *range.end();
        self.subsequence(Int(start as i128), Int((end + 1) as i128))
    }
}

impl<T: Clone> IndexLogic<RangeToInclusive<usize>> for Seq<T> {
    type Item = Seq<T>;

    fn index_logic(self, range: RangeToInclusive<usize>) -> Self::Item {
        self.subsequence(Int(0), Int((range.end + 1) as i128))
    }
}
