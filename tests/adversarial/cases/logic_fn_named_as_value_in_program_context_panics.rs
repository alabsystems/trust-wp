//@ expect: reject
//@ mechanism: a `#[logic]` function's run-time body is `unreachable!("logic functions are erased at
//@ mechanism: runtime")` (`logic_emit::emit_logic_function`), and program code that calls one is
//@ mechanism: refused, but the program logic-call validator (`ProgramLogicCallValidator`) reads only a
//@ mechanism: call's callee and a method call. Named as a value and handed to `Option::map`, the logic
//@ mechanism: function runs inside `map`, where no check looks, and the verifier reads the call as the
//@ mechanism: function's logical definition. The sibling of
//@ mechanism: ghost_extraction_named_as_value_in_program_context_panics in the logic-call validator,
//@ mechanism: whose snapshot recognisers D-193 rewrote; found probing them sideways.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a logic function named as a
//@ fixed-by: value outside a snapshot or ghost block is refused as a call to it is (`call_instantiation`
//@ fixed-by: reads a function named as a value).
//@ accept-means: a program body that hands a logic function to `Option::map` is credited `verified`,
//@ accept-means: though the call reaches `unreachable!()`.
//@ WHY THE CONTRACT IS FALSE: `map_logic` and `map_pred` panic on every call ("internal error: entered
//@ WHY THE CONTRACT IS FALSE: unreachable code: logic functions are erased at runtime").
//@ teeth: MEASURED on the debug driver of wp-s150 with D-193: both functions verified (a third,
//@ teeth: asserting the mapped value, is unknown on a quantifier and is not here). Natively, built
//@ teeth: against trust-wp-std, `map_logic` exits 101 with that panic. The callee-only check is older
//@ teeth: than D-193, so the campaign tip credits both too (not run).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn lf(x: i32) -> i32 {
    x
}

#[logic]
pub fn lp(x: i32) -> bool {
    x == x
}

#[ensures(result)]
pub fn map_logic() -> bool {
    let _r: Option<i32> = Some(5i32).map(lf);
    true
}

#[ensures(result)]
pub fn map_pred() -> bool {
    let _r: Option<bool> = Some(5i32).map(lp);
    true
}
