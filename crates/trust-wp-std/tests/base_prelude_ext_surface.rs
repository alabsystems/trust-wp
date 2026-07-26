// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[allow(dead_code)]
mod base_prelude_ext_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let arr = [1_i32, 2, 3];

        let _ = 'x'.to_utf8();
        let _ = 7_u32.leading_zeros_logic();
        let _ = Some(1_i32).map_logic(Mapping::cst(2_i32));
        let _ = arr[..].to_ref_seq();

        let p: *const [i32] = &arr;
        let _ = p.thin();

        let q: *const i32 = arr.as_ptr();
        let _ = unsafe { q.add_live(0, Ghost::conjure()) };
    }
}

#[test]
#[allow(clippy::assertions_on_constants)]
fn prelude_reexports_base_ext_traits() {
    assert!(true);
}
