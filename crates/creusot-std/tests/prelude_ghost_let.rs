// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use creusot_std::prelude::*;

struct Wrapper(i32);

fn _ghost_let_reborrow_shape(g: Ghost<&mut Wrapper>) {
    ghost_let!(g2 = &mut g.into_inner().0);
    let _: Ghost<&mut i32> = g2;
}

#[test]
#[allow(clippy::assertions_on_constants, clippy::no_effect_underscore_binding)]
fn prelude_reexports_ghost_let_macro() {
    // This test intentionally checks compile-time macro visibility/type shape.
    let w = Wrapper(0);
    let _n = w.0;
    assert!(true);
}
