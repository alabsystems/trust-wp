// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Range<T>` iterator spec implementations.
//!
//! In Creusot, Range implements `IteratorSpec` via the nightly `Step` trait.
//! Since trust-wp targets stable Rust, we expand for each concrete integer type.
//!
//! The `produces` body is a content-aware arithmetic formula:
//! - end is preserved across the transition
//! - start monotonically increases
//! - visited length equals the start difference
//! - each visited element equals start + index
//!
//! The driver rewrite in `iterator_spec_rewrite/range.rs` provides the
//! equivalent formula for SMT encoding using `start_log()` / `end_log()`
//! accessors. The Rust body here is a runtime-testable approximation.
//!
//! Reference: Creusot `creusot-std/src/std/iter/range.rs`

use super::IteratorSpec;
use crate::logic::{Int, Seq};

/// Macro to implement `IteratorSpec` for `Range<$ty>` across integer types.
macro_rules! impl_range_iterator_spec {
    ( $( $ty:ty ),+ ) => {
        $(
            #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss, clippy::cast_lossless)]
            impl IteratorSpec for std::ops::Range<$ty> {
                fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
                    // Content-aware range formula:
                    // 1. end preserved
                    let end_eq = self.end == o.end;
                    // 2. start monotonically increases
                    let start_le = (self.start as i128) <= (o.start as i128);
                    // 3. visited length == start difference
                    let len_eq = visited.len()
                        == Int((o.start as i128) - (self.start as i128));
                    // 4. element identity: visited[i] == self.start + i
                    let n = visited.len().0 as usize;
                    let elems_ok = (0..n).all(|i| {
                        (visited[i] as i128) == (self.start as i128) + (i as i128)
                    });
                    end_eq && start_le && len_eq && elems_ok
                }

                fn completed(&mut self) -> bool {
                    self.start >= self.end
                }
            }
        )+
    };
}

impl_range_iterator_spec! { i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize }

/// Macro to implement `IteratorSpec` for `RangeInclusive<$ty>` across integer types.
///
/// `RangeInclusive` uses `start()..=end()` accessors instead of public fields.
/// The `produces` body is a length-conservation approximation (the total number
/// of elements across `visited` and the remaining range is preserved).
/// The `completed` check uses `*self.start() > *self.end()` to avoid nightly
/// ambiguity between `RangeInclusive::is_empty` and `ExactSizeIterator::is_empty`.
macro_rules! impl_range_inclusive_iterator_spec {
    ( $( $ty:ty ),+ ) => {
        $(
            #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss, clippy::cast_lossless)]
            impl IteratorSpec for std::ops::RangeInclusive<$ty> {
                fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
                    // Length-conservation: total elements = visited + remaining
                    let self_len = if *self.start() <= *self.end() {
                        (*self.end() as i128) - (*self.start() as i128) + 1
                    } else {
                        0i128
                    };
                    let o_len = if *o.start() <= *o.end() {
                        (*o.end() as i128) - (*o.start() as i128) + 1
                    } else {
                        0i128
                    };
                    self_len == visited.len().0 + o_len
                }

                fn completed(&mut self) -> bool {
                    *self.start() > *self.end()
                }
            }
        )+
    };
}

impl_range_inclusive_iterator_spec! { i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize }
