// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_std::logic::FMap;

/// Consume a mutable borrow so the split handle can be used without stacked
/// borrows aliasing on the pinned entry.
fn end_borrow<T>(_: T) {}

#[test]
#[should_panic(expected = "exceed pre-reserved capacity")]
fn test_fmap_ghost_split_insert_panics_when_reservation_is_exhausted() {
    let mut map: FMap<i32, i32> = FMap::empty().insert(1, 10).insert(2, 20);
    let (value, mut split) = map.split_mut_ghost(&1);

    assert_eq!(*value, 10);
    end_borrow(value);

    for key in 100..200 {
        split.insert_ghost(key, key * 10);
    }
}
