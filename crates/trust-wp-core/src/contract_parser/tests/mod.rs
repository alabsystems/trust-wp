// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    BinOp, ExprSort, Pattern, UnOp,
};

mod helpers;
use helpers::*;

mod advanced_syntax;
mod basics;
mod blocks_and_let;
mod conditionals;
mod creusot_compat;
mod edge_cases;
mod float_and_ascription;
mod indexing_and_fields;
mod logic_fns;
mod matching;
mod performance;
mod quantifiers;
mod regressions;
mod spanned_parity;
mod view_and_methods;
