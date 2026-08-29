// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    call_resolve_shared::{classify_cell_builtin_path, CellBuiltin},
    *,
};
#[test]
fn is_box_new_call_path_matches_box_constructor_only() {
    assert!(is_box_new_call_path("alloc::boxed::Box::<i32>::new"));
    assert!(is_box_new_call_path("std::boxed::Box::<u64>::new"));
    assert!(!is_box_new_call_path("alloc::boxed::Box::<i32>::from"));
    assert!(!is_box_new_call_path("alloc::vec::Vec::<i32>::new"));
}

#[test]
fn classify_try_self_adt_path_recognizes_option_variants() {
    assert_eq!(classify_try_self_adt_path("Option"), Some(true));
    assert_eq!(
        classify_try_self_adt_path("std::option::Option"),
        Some(true)
    );
    assert_eq!(
        classify_try_self_adt_path("core::option::Option"),
        Some(true)
    );
}

#[test]
fn classify_try_self_adt_path_recognizes_result_variants() {
    assert_eq!(classify_try_self_adt_path("Result"), Some(false));
    assert_eq!(
        classify_try_self_adt_path("std::result::Result"),
        Some(false)
    );
    assert_eq!(
        classify_try_self_adt_path("core::result::Result"),
        Some(false)
    );
}

#[test]
fn classify_try_self_adt_path_rejects_unsupported_try_impls() {
    assert_eq!(
        classify_try_self_adt_path("core::ops::control_flow::ControlFlow"),
        None
    );
    assert_eq!(classify_try_self_adt_path("core::task::Poll"), None);
}

#[test]
fn is_try_branch_path_recognizes_trait_method_paths() {
    assert!(is_try_branch_path("std::ops::Try::branch"));
    assert!(is_try_branch_path("core::ops::try_trait::Try::branch"));
    assert!(is_try_branch_path(
        "<std::option::Option<i32> as std::ops::Try>::branch"
    ));
}

#[test]
fn is_try_branch_path_rejects_non_branch_paths() {
    assert!(!is_try_branch_path("std::ops::Try::from_output"));
    assert!(!is_try_branch_path("core::result::Result::ok"));
    assert!(!is_try_branch_path("core::option::Option::unwrap"));
    // Regression: trait names ending in "Try" must not match (#1426)
    assert!(!is_try_branch_path(
        "<crate::foo::Bar as crate::foo::NotTry>::branch"
    ));
}

#[test]
fn classify_cell_builtin_path_normalizes_creusot_aliases() {
    assert_eq!(
        classify_cell_builtin_path("creusot_std::cell::PredCell::<u32>::as_slice_of_cells"),
        Some(CellBuiltin::PredCellAsSliceOfCells)
    );
    assert_eq!(
        classify_cell_builtin_path("creusot_std::cell::PermCell::<i32>::borrow_mut"),
        Some(CellBuiltin::PermCellBorrowMut)
    );
}

#[test]
fn classify_cell_builtin_path_matches_new_predcell_variants() {
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::std::cell::PredCell::<u32>::swap"),
        Some(CellBuiltin::PredCellSwap)
    );
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::cell::PredCell::<u32>::into_inner"),
        Some(CellBuiltin::PredCellIntoInner)
    );
    assert_eq!(
        classify_cell_builtin_path("creusot_std::cell::PredCell::<u32>::update"),
        Some(CellBuiltin::PredCellUpdate)
    );
}

#[test]
fn classify_cell_builtin_path_matches_permcell_set() {
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::std::cell::PermCell::<i32>::set"),
        Some(CellBuiltin::PermCellSet)
    );
    assert_eq!(
        classify_cell_builtin_path("creusot_std::cell::PermCell::<i32>::set"),
        Some(CellBuiltin::PermCellSet)
    );
}

#[test]
fn classify_cell_builtin_path_matches_take_and_from_mut() {
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::std::cell::PredCell::<u32>::take"),
        Some(CellBuiltin::PredCellTake)
    );
    assert_eq!(
        classify_cell_builtin_path("creusot_std::cell::PredCell::<u32>::take"),
        Some(CellBuiltin::PredCellTake)
    );
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::cell::PermCell::<i32>::take"),
        Some(CellBuiltin::PermCellTake)
    );
    assert_eq!(
        classify_cell_builtin_path("creusot_std::cell::PermCell::<i32>::take"),
        Some(CellBuiltin::PermCellTake)
    );
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::std::cell::PermCell::<i32>::from_mut"),
        Some(CellBuiltin::PermCellFromMut)
    );
    assert_eq!(
        classify_cell_builtin_path("creusot_std::cell::PermCell::<i32>::from_mut"),
        Some(CellBuiltin::PermCellFromMut)
    );
}

#[test]
fn classify_cell_builtin_path_matches_perm_ward() {
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::ghost::perm::Perm::<u32>::ward"),
        Some(CellBuiltin::PermWard)
    );
    assert_eq!(
        classify_cell_builtin_path("creusot_std::Perm::<u32>::ward"),
        Some(CellBuiltin::PermWard)
    );
}

#[test]
fn classify_cell_builtin_path_rejects_non_cell_methods() {
    assert_eq!(
        classify_cell_builtin_path("core::cell::Cell::<u32>::get"),
        None
    );
    assert_eq!(
        classify_cell_builtin_path("trust_wp_std::logic::Mapping::<u32, bool>::get"),
        None
    );
}
