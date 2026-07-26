// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for sort conversion helpers.

use super::{SortConversionError, VarSort};
use crate::formula::ExprSort;

#[test]
fn test_var_sort_try_from_expr_sort() {
    assert_eq!(VarSort::try_from(ExprSort::Int), Ok(VarSort::Int));
    assert_eq!(VarSort::try_from(ExprSort::Bool), Ok(VarSort::Bool));
    assert_eq!(VarSort::try_from(ExprSort::Seq), Ok(VarSort::Seq));
    assert_eq!(
        VarSort::try_from(ExprSort::Unit),
        Err(SortConversionError::UnitHasNoVarSort)
    );
    assert_eq!(
        VarSort::try_from(ExprSort::Datatype(0)),
        Err(SortConversionError::NoVarSortEquivalent)
    );
    assert_eq!(
        VarSort::try_from(ExprSort::FMap),
        Err(SortConversionError::NoVarSortEquivalent)
    );
    assert_eq!(
        VarSort::try_from(ExprSort::Tuple(2)),
        Err(SortConversionError::NoVarSortEquivalent)
    );
    assert_eq!(
        VarSort::try_from(ExprSort::Ref(Box::new(ExprSort::Int))),
        Err(SortConversionError::NoVarSortEquivalent)
    );
    assert_eq!(
        VarSort::try_from(ExprSort::MutRef(Box::new(ExprSort::Int))),
        Err(SortConversionError::NoVarSortEquivalent)
    );
}

#[test]
fn test_expr_sort_from_var_sort() {
    assert_eq!(ExprSort::from(VarSort::Int), ExprSort::Int);
    assert_eq!(ExprSort::from(VarSort::Bool), ExprSort::Bool);
    assert_eq!(ExprSort::from(VarSort::Seq), ExprSort::Seq);
}

#[test]
fn test_var_sort_from_expr_sort() {
    assert_eq!(VarSort::from_expr_sort(None), VarSort::Int);
    assert_eq!(
        VarSort::from_expr_sort(Some(&ExprSort::Bool)),
        VarSort::Bool
    );
    assert_eq!(VarSort::from_expr_sort(Some(&ExprSort::Seq)), VarSort::Seq);
    // Non-VarSort variants fall back to Int
    assert_eq!(
        VarSort::from_expr_sort(Some(&ExprSort::Datatype(0))),
        VarSort::Int
    );
    assert_eq!(
        VarSort::from_expr_sort(Some(&ExprSort::TypeParam(0))),
        VarSort::Int
    );
}
