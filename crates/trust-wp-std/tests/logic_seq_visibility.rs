// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for Creusot-compat Seq lemma visibility.
//!
//! This must compile from an external crate context, so we keep it as an
//! integration test rather than a unit test under `logic::seq`.

use trust_wp_std::{logic::seq::flat_map_singleton, prelude::*};

#[test]
fn test_flat_map_singleton_is_publicly_reachable() {
    flat_map_singleton::<i32, i32>();
    let _ = <Seq<i32>>::flat_map_singleton::<i32>;
}
