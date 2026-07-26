// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-time regression test for nested `Self` replacement in `extern_spec!`.

use trust_wp_macros::extern_spec;

trait NestedSelfSpec {
    fn nested(
        &self,
        a: Option<Self>,
        b: &mut Self,
        c: Vec<Self>,
        d: Vec<(Self, &Self)>,
    ) -> Option<Self>
    where
        Self: Sized;
}

impl NestedSelfSpec for String {
    fn nested(
        &self,
        _a: Option<Self>,
        _b: &mut Self,
        _c: Vec<Self>,
        _d: Vec<(Self, &Self)>,
    ) -> Option<Self> {
        Some(self.clone())
    }
}

extern_spec! {
    impl NestedSelfSpec for String {
        fn nested(
            &self,
            a: Option<Self>,
            b: &mut Self,
            c: Vec<Self>,
            d: Vec<(Self, &Self)>,
        ) -> Option<Self>;
    }
}

#[test]
fn extern_spec_trait_impl_supports_nested_self_types() {
    let recv = String::from("recv");
    let mut x = String::from("x");
    let pair_ref = String::from("pair-ref");
    let result = <String as NestedSelfSpec>::nested(
        &recv,
        Some(String::from("a")),
        &mut x,
        vec![String::from("v")],
        vec![(String::from("owner"), &pair_ref)],
    );
    assert_eq!(result, Some(String::from("recv")));
}
