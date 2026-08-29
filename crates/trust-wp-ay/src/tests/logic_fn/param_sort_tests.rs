// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic Function Parameter Sort Tests (#544 Phase 3)
//!
//! Seq inference nesting tests (Old, Final, Exists, Let, View, LetAssume)
//! are in param_sort_seq_inference.rs.

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

mod apply_logic_fn_coercions;
mod cross_function_param_sort_hints;
mod datatype_passthrough;
mod datatype_sort_overrides_seq_hint;
