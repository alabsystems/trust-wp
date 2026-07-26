// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_std::{
    ghost::{perm::Perm, Ghost, Snapshot},
    std::cell::{PermCell, PredCell},
};

#[test]
fn pred_cell_from_mut_updates_backing_scalar() {
    let mut value = 5_i32;

    {
        let cell = PredCell::from_mut(&mut value, Snapshot::capture(&()));
        assert_eq!(cell.get(), 5);
        cell.set(9);
        assert_eq!(cell.get(), 9);
    }

    assert_eq!(value, 9);
}

#[test]
fn pred_cell_slice_view_mutates_original_slice() {
    let mut data = [1_i32, 2, 3];

    {
        let slice_cell = PredCell::from_mut(&mut data[..], Snapshot::capture(&()));
        let cells = slice_cell.as_slice_of_cells(Snapshot::capture(&()));

        cells[1].set(99);
        assert_eq!(cells[1].get(), 99);
    }

    assert_eq!(data, [1, 99, 3]);
}

#[test]
fn perm_cell_from_mut_aliases_original_value() {
    let mut value = 10_i32;
    let raw = core::ptr::addr_of_mut!(value);

    {
        let (cell, perm_mut) = PermCell::from_mut(&mut value);
        assert_eq!(cell.as_ptr(), raw);

        // SAFETY: This token was created by `from_mut` for this exact cell.
        unsafe {
            cell.set(perm_mut, 41);
        }

        // SAFETY: In this runtime test we only observe the same cell after the write above.
        unsafe {
            assert_eq!(cell.get(Ghost::<&Perm<PermCell<i32>>>::conjure()), 41);
        }
    }

    assert_eq!(value, 41);
}
