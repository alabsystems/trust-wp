// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Once<T>` iterator spec implementation.
//!
//! `std::iter::once(value)` produces an iterator that yields exactly one element.
//! After that element is consumed, the iterator is completed.
//!
//! Reference: Creusot `creusot-std/src/std/iter/once.rs`

use super::IteratorSpec;
use crate::logic::{Int, Seq};

impl<T: PartialEq> IteratorSpec for std::iter::Once<T> {
    fn produces(self, visited: Seq<Self::Item>, _o: Self) -> bool {
        // Either nothing produced yet, or exactly one element produced
        visited.is_empty() || visited.len() == Int(1)
    }

    fn completed(&mut self) -> bool {
        // Once is completed when its internal Option is None.
        // At runtime we cannot inspect the private field, so this is a
        // placeholder — the driver rewrite provides the real semantics.
        false
    }
}
