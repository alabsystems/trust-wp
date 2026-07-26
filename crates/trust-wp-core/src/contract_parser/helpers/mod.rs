// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parser helper methods, organized by category.
//!
//! All submodules add `impl ContractParser<'_>` methods. The parent
//! `contract_parser` module sees them via the `pub(in crate::contract_parser)`
//! visibility qualifier.

mod expressions;
mod identifiers;
mod literals;
mod patterns;
mod quantifiers;
mod tokenizer;
