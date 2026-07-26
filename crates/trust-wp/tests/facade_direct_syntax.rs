// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Facade import-path regression tests for direct contract syntax.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod wildcard_import {
    use trust_wp::*;

    #[requires(v.len() > 0)]
    #[ensures(result == old(v.len()) - 1)]
    pub fn pop_and_return_len(v: &mut Vec<i32>) -> usize {
        v.pop();
        v.len()
    }
}

#[allow(dead_code)]
mod wildcard_import_resolve_surface {
    use trust_wp::*;

    #[allow(clippy::trivially_copy_pass_by_ref)] // Testing resolve(&T) API surface
    pub fn typecheck(x: &i32) -> bool {
        resolve(x)
    }
}

mod prelude_import {
    use trust_wp::prelude::*;

    #[requires(v.len() > 0)]
    #[ensures(result == old(v.len()) - 1)]
    pub fn pop_and_return_len(v: &mut Vec<i32>) -> usize {
        v.pop();
        v.len()
    }
}

#[allow(dead_code)]
mod prelude_import_resolve_surface {
    use trust_wp::prelude::*;

    #[allow(clippy::trivially_copy_pass_by_ref)] // Testing resolve(&T) API surface
    pub fn typecheck(x: &i32) -> bool {
        resolve(x)
    }
}

#[allow(dead_code)]
mod wildcard_import_open_inv_result {
    use trust_wp::*;

    #[open_inv_result]
    pub fn make_value() -> u64 {
        42
    }
}

#[allow(dead_code)]
mod prelude_import_open_inv_result {
    use trust_wp::prelude::*;

    #[open_inv_result]
    pub fn make_value() -> u64 {
        42
    }
}

#[allow(dead_code)]
mod wildcard_import_default_surface {
    use trust_wp::*;

    // `self::Default` proves the glob-imported facade export resolved
    // in this module, not the standard library prelude.
    #[derive(self::Default)]
    enum Wrapper {
        #[default]
        A(i32, bool),
        B,
    }

    fn typecheck() -> Wrapper {
        Wrapper::default()
    }
}

#[allow(dead_code)]
mod prelude_import_default_surface {
    use trust_wp::prelude::*;

    #[derive(self::Default)]
    enum Wrapper {
        #[default]
        A(i32, bool),
        B,
    }

    fn typecheck() -> Wrapper {
        Wrapper::default()
    }
}

#[test]
fn test_facade_direct_syntax_import_paths_compile() {
    let mut wildcard_vec = vec![1, 2, 3];
    assert_eq!(wildcard_import::pop_and_return_len(&mut wildcard_vec), 2);

    let mut prelude_vec = vec![4, 5, 6];
    assert_eq!(prelude_import::pop_and_return_len(&mut prelude_vec), 2);
}
