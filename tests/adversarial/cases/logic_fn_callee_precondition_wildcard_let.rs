//@ expect: reject
//@ mechanism: `let _ = needs_pos(x);` binds nothing, and the contract parser's `let` desugaring dropped the value, so the call vanished from the parsed logic body and no goal could owe it. Where statements are preserved (a logic body) the value is now kept as a `$stmt` binding (`contract_parser` `desugar_let_statement`), as Creusot's vcgen reads `let _ = e; rest` through `e`.
//@ accept-means: a call whose value is bound to `_` is never owed.
//@ WHY IT IS FALSE: at `x == 0` the body evaluates `needs_pos(0)`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓`, the call never examined. With the lane owing the precondition but the parser dropping `let _`'s value, `caller verified ✓` too.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(x: Int) -> Int {
    let _ = needs_pos(x);
    0
}
