// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `MapInv` iterator adapter — maps with access to production history.
//!
//! Reference: `creusot-std/src/std/iter/map_inv.rs`

use crate::{ghost::Snapshot, logic::Seq};

/// Iterator adapter that maps with access to production history.
///
/// Created by [`super::IteratorSpec::map_inv`]. Wraps an inner iterator and a closure
/// that receives both the current element and a `Snapshot` of all previously
/// produced elements.
///
/// Reference: `creusot-std/src/std/iter/map_inv.rs`
pub struct MapInv<I: Iterator, F> {
    /// The inner iterator being adapted.
    pub iter: I,
    /// The mapping closure.
    pub func: F,
    /// Ghost snapshot of elements produced so far (zero-sized at runtime).
    pub produced: Snapshot<Seq<I::Item>>,
}

impl<I, B, F> Iterator for MapInv<I, F>
where
    I: Iterator,
    F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B,
{
    type Item = B;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                let r = (self.func)(v, self.produced);
                Some(r)
            }
            None => None,
        }
    }
}
