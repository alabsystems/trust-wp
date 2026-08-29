// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use std::sync::Arc;

use ntest::timeout;

use super::{super::*, helpers::*};

mod match_encoding_tests {
    use trust_wp_core::formula::Pattern;

    use super::*;
    use crate::encoder::match_enc::SwitchTarget;
    mod basic_patterns;
    mod enum_signed_range_tests;
    mod field_range_constraints;
    mod nested_patterns;
    mod option_preseed_regressions;
    mod predeclared_datatype_regressions;
    mod result_constructor_tests;
    mod signed_field_range_tests;
    mod struct_native_selectors;
    mod tuple_patterns;
    mod user_defined_enum_tests;
}
