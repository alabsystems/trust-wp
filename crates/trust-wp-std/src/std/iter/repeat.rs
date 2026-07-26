// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Repeat<T>` iterator spec implementation.
//!
//! `std::iter::repeat(value)` produces an infinite iterator that always yields
//! clones of `value`. It never completes.
//!
//! Reference: Creusot `creusot-std/src/std/iter/repeat.rs`

use super::IteratorSpec;
use crate::logic::Seq;

impl<T: Clone> IteratorSpec for std::iter::Repeat<T> {
    fn produces(self, _visited: Seq<Self::Item>, _o: Self) -> bool {
        // Placeholder: the driver rewrite provides the real element-identity
        // semantics (forall<i> visited[i] == repeat@).
        true
    }

    fn completed(&mut self) -> bool {
        // Repeat never completes
        false
    }
}
