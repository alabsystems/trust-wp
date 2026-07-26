// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[allow(dead_code)]
mod prelude_resolve_surface {
    use trust_wp_std::prelude::*;

    #[allow(clippy::trivially_copy_pass_by_ref)] // Testing resolve(&T) API surface
    pub fn typecheck(x: &i32) -> bool {
        resolve(x)
    }
}

#[test]
#[allow(clippy::assertions_on_constants)]
fn prelude_reexports_resolve() {
    assert!(true);
}
