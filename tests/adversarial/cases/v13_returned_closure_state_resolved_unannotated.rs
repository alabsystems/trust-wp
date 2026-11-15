//@ expect: reject
//@ mechanism: v12_returned_closure_state_resolved_by_its_binding with the binder's type dropped
//@ mechanism: (`exists<g>`). The contract parser gives the binder no sort, and an unannotated binder kept
//@ mechanism: the legacy collapse of `^g` onto the binder, so `resolve(g)` of the state the function
//@ mechanism: returns was `true`.
//@ accept-means: a function that RETURNS the closure after calling it is credited with the claim that
//@ accept-means: the returned state's captured borrows are resolved.
//@ WHY THE CONTRACT IS FALSE: `keep_closure_unann` returns the state `g` it reached; a closure
//@ WHY THE CONTRACT IS FALSE: capturing `&mut x` keeps that borrow in `g`, and its caller decides the
//@ WHY THE CONTRACT IS FALSE: borrow's final value by calling the returned closure again.
//@ fixed-by: D-127 (the final value of a binder a written `forall`/`exists` binds is refused unless
//@ fixed-by: its annotation certifies a sort holding no borrow)
//@ teeth: MEASURED (debug driver): before D-127 keep_closure_unann verified; D-127 refuses it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

#[requires(f.precondition(()))]
#[ensures(exists<g> f.postcondition_mut((), g, ()) && resolve(g))]
pub fn keep_closure_unann<F: FnMut()>(mut f: F) -> F {
    f();
    f
}
