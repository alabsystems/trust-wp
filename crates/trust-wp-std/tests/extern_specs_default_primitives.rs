// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

const EXTERN_SPECS_SOURCE: &str = include_str!("../src/std/extern_specs.rs");

fn assert_default_contract(ty: &str, ensures: &str) {
    let expected_block = format!(
        "impl core::default::Default for {ty} {{\n        #[ensures(result == {ensures})]\n        fn default() -> {ty};\n    }}"
    );
    assert!(
        EXTERN_SPECS_SOURCE.contains(&expected_block),
        "missing default extern spec block for {ty}: {expected_block}"
    );
}

#[test]
fn primitive_default_extern_specs_cover_i128_and_u128() {
    assert_default_contract("i128", "0i128");
    assert_default_contract("u128", "0u128");
}
