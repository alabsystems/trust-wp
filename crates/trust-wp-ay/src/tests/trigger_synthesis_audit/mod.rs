// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Audit tests for trigger synthesis edge cases.
//!
//! Verifies trigger synthesis behavior through the public `encode_pure` API:
//! - Existential quantifiers (not just forall)
//! - Mixed forall/exists nesting
//! - Closure bodies
//! - Nested quantifier isolation (inner bodies excluded from outer triggers)
//! - Bool expansion and De Morgan transform interaction
//! - Closure spec and postcondition_mut interaction
//!
//! Re: #1018 (trigger synthesis), #970 (closure specs)

mod bool_expansion_and_demorgan;
mod closure_and_postcondition_mut;
mod fixtures;
mod quantifier_nesting;
mod wrapper_paths;
