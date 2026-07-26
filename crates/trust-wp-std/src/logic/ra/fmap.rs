// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FMap Resource Algebra
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Compile-surface stub matching Creusot's `creusot_std::logic::ra::fmap` module.
//! Provides the `FMapInsertLocalUpdate` type used by concurrent data structure
//! examples (e.g., `persistent_array.rs`).
//!
//! Source: Creusot `creusot-std/src/logic/ra/fmap.rs`

use std::hash::Hash;

use super::update::LocalUpdate;
use crate::{ghost::Snapshot, logic::FMap};

/// Insert a key-value pair into an authority/fragment pair of [`FMap`]s.
///
/// Requires that the key is not yet in the authority map.
///
/// Source: Creusot `creusot-std/src/logic/ra/fmap.rs:148`
pub struct FMapInsertLocalUpdate<K, V>(pub Snapshot<K>, pub Snapshot<V>);

impl<K, V> LocalUpdate<FMap<K, V>> for FMapInsertLocalUpdate<K, V>
where
    K: Eq + Hash,
{
    #[crate::logic(open)]
    fn premise(&self, from_auth: &FMap<K, V>, _from_frag: &FMap<K, V>) -> bool {
        !from_auth.contains(self.0.into_inner())
    }

    #[crate::logic(open)]
    fn update(&self, from_auth: FMap<K, V>, from_frag: FMap<K, V>) -> (FMap<K, V>, FMap<K, V>) {
        (
            from_auth.insert(self.0.into_inner(), self.1.into_inner()),
            from_frag.insert(self.0.into_inner(), self.1.into_inner()),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fmap_insert_local_update_exists() {
        // Type existence check — the struct is used in Creusot examples
        // as a type parameter, not called at runtime.
        let _: fn(Snapshot<u32>, Snapshot<i32>) -> FMapInsertLocalUpdate<u32, i32> =
            |k, v| FMapInsertLocalUpdate(k, v);
    }
}
