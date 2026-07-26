// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[allow(dead_code)]
mod base_prelude_ext_surface {
    use creusot_std::prelude::*;

    // #2573: verify that FnOnceExt/FnMutExt/FnExt/IndexLogic anonymous
    // re-exports compile without conflict.
    //
    // Since `as _` imports do not bring trait names into the namespace,
    // we verify via explicit import that the traits are accessible through
    // the creusot-std crate path (the prelude adds them anonymously for
    // method resolution by trust-wp's contract system).
    fn typecheck_closure_and_index_logic() {
        use creusot_std::trust_wp_std::std::ops::{FnExt, FnMutExt, FnOnceExt};

        fn accepts_fn_once_ext<F: FnOnceExt<(u32,)>>(_f: F) {}
        accepts_fn_once_ext(|_x: u32| true);

        fn accepts_fn_mut_ext<F: FnMutExt<(u32,)>>(_f: F) {}
        accepts_fn_mut_ext(|_x: u32| true);

        fn accepts_fn_ext<F: FnExt<(u32,)>>(_f: F) {}
        accepts_fn_ext(|_x: u32| true);

        use creusot_std::trust_wp_std::logic::ops::IndexLogic;
        fn _requires_index_logic<T: IndexLogic<usize>>(_t: &T) {}
    }

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
