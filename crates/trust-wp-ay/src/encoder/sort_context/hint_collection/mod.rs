// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort hint collection: Bool and collection hint accumulation from AST traversals.

mod accumulator;
mod bool_hints;

#[cfg(any(test, feature = "sep-logic"))]
pub(in crate::encoder::sort_context) use accumulator::collect_formula_sort_hints;
pub(crate) use accumulator::{collect_all_sort_hints, SortHintAccumulator};
pub(crate) use bool_hints::collect_bool_hints;
pub(in crate::encoder) use bool_hints::{
    collect_names_as_bool, receiver_qualified_method_hint_key,
};
