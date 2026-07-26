// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-surface test for range-helper facade parity (#2519).
//!
//! Verifies that the range-helper types and functions from
//! `creusot_std::std::ops` resolve correctly through the facade.
//! This is a compile-surface test — it exercises type-checking, not
//! runtime behavior (the logic helpers panic at runtime).

#[allow(dead_code)]
mod ops_surface {
    use core::ops::{
        Bound, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
    };

    use creusot_std::std::ops::{
        between, lower_bound, upper_bound, RangeBounds, RangeInclusiveExt,
    };

    // -- Trait bound witnesses --

    fn require_range_bounds<R: RangeBounds<i32>>(_r: &R) {}
    fn require_range_inclusive_ext<R: RangeInclusiveExt<i32>>() {}

    // -- Typecheck stable range types satisfy RangeBounds --

    fn typecheck_range_bounds() {
        let full = ..;
        require_range_bounds::<RangeFull>(&full);

        let from = 1..;
        require_range_bounds::<RangeFrom<i32>>(&from);

        let to = ..10;
        require_range_bounds::<RangeTo<i32>>(&to);

        let range = 1..10;
        require_range_bounds::<Range<i32>>(&range);

        let inclusive = 1..=10;
        require_range_bounds::<RangeInclusive<i32>>(&inclusive);

        let to_inclusive = ..=10;
        require_range_bounds::<RangeToInclusive<i32>>(&to_inclusive);

        let tuple = (Bound::Included(1), Bound::Excluded(10));
        require_range_bounds::<(Bound<i32>, Bound<i32>)>(&tuple);
    }

    // -- Typecheck RangeInclusiveExt --

    fn typecheck_range_inclusive_ext() {
        require_range_inclusive_ext::<RangeInclusive<i32>>();
    }

    // -- Typecheck free helper function signatures --

    fn typecheck_helpers(_lo: Bound<i32>, _item: i32, _hi: Bound<i32>) {
        // These are spec-only; just verify the signatures resolve.
        let _: fn(Bound<i32>, i32, Bound<i32>) -> bool = between;
        let _: fn(Bound<i32>, i32) -> bool = lower_bound;
        let _: fn(i32, Bound<i32>) -> bool = upper_bound;
    }
}

// A real test that exercises the import surface. The logic functions
// panic at runtime, so we only verify compile + import resolution.
#[test]
fn range_ops_facade_compiles() {
    // The ops_surface module above type-checks at compile time.
    // This test function exists so `cargo test` reports a pass.
}
