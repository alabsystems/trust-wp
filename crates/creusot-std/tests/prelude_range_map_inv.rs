// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use creusot_std::prelude::{vec, *};

fn build_rows(size: usize) -> vec::Vec<vec::Vec<usize>> {
    (0..size).map_inv(|_, _| vec![0; size]).collect()
}

#[test]
fn prelude_range_map_inv_collects_vec_rows() {
    let size = 4usize;
    let rows = build_rows(size);

    assert_eq!(rows.len(), size);
    assert!(rows.iter().all(|row| row.len() == size));
    assert!(rows.iter().flatten().all(|cell| *cell == 0));
}
