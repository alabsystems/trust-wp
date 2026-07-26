// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_std::prelude::*;

#[test]
fn vec_view_spec_from_prelude_is_borrowed() {
    let v = vec![1, 2, 3];
    let seq: Seq<i32> = v.view_spec();

    assert_eq!(seq.len().0, 3);
    assert_eq!(v.len(), 3);
}

#[test]
fn string_view_spec_from_prelude_is_borrowed() {
    let s = String::from("abc");
    let seq = s.view_spec();

    assert_eq!(seq.len().0, 3);
    assert_eq!(s.len(), 3);
}
