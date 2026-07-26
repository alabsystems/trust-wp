// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared sort conversion helpers for SMT encoding.

use std::{error::Error, fmt};

use crate::formula::ExprSort;

/// SMT sort for variables.
///
/// Relationship to other sort enums:
/// - `VarSort` models only SMT declaration sorts (`Int`/`Bool`/`Seq`)
/// - `ExprSort` additionally includes `Unit`, which has no `VarSort` equivalent
/// - `ParamSortHint` is an override-only subset (`Bool`/`Seq`/`Datatype`)
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarSort {
    /// Integer sort
    Int,
    /// Boolean sort
    Bool,
    /// Sequence sort (for view variables)
    Seq,
}

/// Conversion error from `ExprSort` to `VarSort`.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortConversionError {
    /// `ExprSort::Unit` is a singleton type and cannot be declared as a variable sort.
    UnitHasNoVarSort,
    /// `ExprSort` variant has no direct `VarSort` equivalent (Datatype, `FMap`, Tuple, Ref, MutRef).
    NoVarSortEquivalent,
}

impl fmt::Display for SortConversionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnitHasNoVarSort => formatter.write_str("Unit type has no VarSort equivalent"),
            Self::NoVarSortEquivalent => {
                formatter.write_str("ExprSort variant has no direct VarSort equivalent")
            }
        }
    }
}

impl Error for SortConversionError {}

impl VarSort {
    /// Convert an optional `ExprSort` into a concrete SMT variable sort.
    ///
    /// `None` is treated as `VarSort::Int` (default sort).
    /// Sorts that don't have a `VarSort` equivalent (Datatype, `FMap`, etc.)
    /// fall back to `VarSort::Int` — the encoder handles the actual ay sort
    /// mapping via `sort_from_expr_sort`.
    #[must_use]
    pub fn from_expr_sort(sort: Option<&ExprSort>) -> Self {
        match sort {
            Some(ExprSort::Bool) => VarSort::Bool,
            Some(ExprSort::Seq) => VarSort::Seq,
            _ => VarSort::Int,
        }
    }
}

impl From<VarSort> for ExprSort {
    fn from(value: VarSort) -> Self {
        match value {
            VarSort::Int => ExprSort::Int,
            VarSort::Bool => ExprSort::Bool,
            VarSort::Seq => ExprSort::Seq,
        }
    }
}

impl TryFrom<ExprSort> for VarSort {
    type Error = SortConversionError;

    fn try_from(value: ExprSort) -> Result<Self, Self::Error> {
        match value {
            ExprSort::Int => Ok(VarSort::Int),
            ExprSort::Bool => Ok(VarSort::Bool),
            ExprSort::Seq => Ok(VarSort::Seq),
            ExprSort::Unit => Err(SortConversionError::UnitHasNoVarSort),
            ExprSort::Datatype(_)
            | ExprSort::FMap
            | ExprSort::Tuple(_)
            | ExprSort::Ref(_)
            | ExprSort::MutRef(_)
            | ExprSort::TypeParam(_)
            | ExprSort::Float => Err(SortConversionError::NoVarSortEquivalent),
        }
    }
}
