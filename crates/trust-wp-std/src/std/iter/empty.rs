// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Empty<T>` iterator spec implementation.
//!
//! `std::iter::empty()` produces an iterator that yields nothing.
//! `produces` is trivially satisfied when visited is empty;
//! `completed` is always true.
//!
//! Reference: Creusot `creusot-std/src/std/iter/empty.rs`

use super::IteratorSpec;
use crate::logic::Seq;

impl<T> IteratorSpec for std::iter::Empty<T> {
    fn produces(self, visited: Seq<Self::Item>, _o: Self) -> bool {
        visited.is_empty()
    }

    fn completed(&mut self) -> bool {
        true
    }
}
