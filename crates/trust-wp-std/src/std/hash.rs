// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for `core::hash` traits (`Hash`, `Hasher`, `BuildHasher`).
//!
//! The `Hash` trait is called implicitly by `HashMap`/`HashSet` operations.
//! Without specs, these calls are classified as opaque (OpaqueCallTrueAssumption),
//! which is unsound. These specs provide a sound generic contract.
//!
//! At the verification level, hashing is modeled abstractly: `Hash::hash`
//! is a pure function that modifies hasher state, and `Hasher::finish`
//! produces a deterministic result. The key property is that equal values
//! produce equal hashes (consistency with PartialEq).

pub mod specs {
    /// Contract for `Hash::hash(&self, state: &mut H)`
    ///
    /// Hash is a total function — it always succeeds and modifies the
    /// hasher state. The key verification property is that hashing is
    /// deterministic: the same value always produces the same hash
    /// sequence on the hasher.
    ///
    /// We model this with a postcondition predicate so the encoder
    /// can reason about hash consistency without needing to model
    /// the actual hash computation.
    pub const HASH: &str = r"
        params: self, state
        ensures: core::hash::Hash::hash.postcondition((self, state), ())
    ";

    /// Contract for `Hash::hash_slice(data: &[Self], state: &mut H)`
    ///
    /// Hashes a slice of values into the hasher state.
    pub const HASH_SLICE: &str = r"
        params: data, state
        ensures: core::hash::Hash::hash_slice.postcondition((data, state), ())
    ";

    /// Contract for `Hasher::finish(&self) -> u64`
    ///
    /// Returns the hash value accumulated in the hasher. This is a
    /// pure function of the hasher state.
    pub const HASHER_FINISH: &str = r"
        ensures: core::hash::Hasher::finish.postcondition((self,), result)
    ";

    /// Contract for `Hasher::write(&mut self, bytes: &[u8])`
    ///
    /// Writes bytes into the hasher state.
    pub const HASHER_WRITE: &str = r"
        params: self, bytes
        ensures: core::hash::Hasher::write.postcondition((self, bytes), ())
    ";

    /// Contract for `Hasher::write_u8(&mut self, i: u8)`
    pub const HASHER_WRITE_U8: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_u8.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_u16(&mut self, i: u16)`
    pub const HASHER_WRITE_U16: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_u16.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_u32(&mut self, i: u32)`
    pub const HASHER_WRITE_U32: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_u32.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_u64(&mut self, i: u64)`
    pub const HASHER_WRITE_U64: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_u64.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_usize(&mut self, i: usize)`
    pub const HASHER_WRITE_USIZE: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_usize.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_i8(&mut self, i: i8)`
    pub const HASHER_WRITE_I8: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_i8.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_i16(&mut self, i: i16)`
    pub const HASHER_WRITE_I16: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_i16.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_i32(&mut self, i: i32)`
    pub const HASHER_WRITE_I32: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_i32.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_i64(&mut self, i: i64)`
    pub const HASHER_WRITE_I64: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_i64.postcondition((self, i), ())
    ";

    /// Contract for `Hasher::write_isize(&mut self, i: isize)`
    pub const HASHER_WRITE_ISIZE: &str = r"
        params: self, i
        ensures: core::hash::Hasher::write_isize.postcondition((self, i), ())
    ";

    /// Contract for `BuildHasher::build_hasher(&self) -> Self::Hasher`
    ///
    /// Creates a new hasher instance. The hasher's initial state is
    /// determined by the BuildHasher.
    pub const BUILD_HASHER: &str = r"
        ensures: core::hash::BuildHasher::build_hasher.postcondition((self,), result)
    ";
}

#[cfg(test)]
mod tests {
    use super::super::test_shim;

    #[test]
    fn test_hash_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::HASH);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("Hash::hash.postcondition"));
    }

    #[test]
    fn test_hash_slice_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::HASH_SLICE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("hash_slice"));
    }

    #[test]
    fn test_hasher_finish_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::HASHER_FINISH);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("finish"));
    }

    #[test]
    fn test_hasher_write_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::HASHER_WRITE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("write"));
    }

    #[test]
    fn test_hasher_write_usize_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::HASHER_WRITE_USIZE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("write_usize"));
    }

    #[test]
    fn test_build_hasher_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BUILD_HASHER);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec.ensures[0].contains("build_hasher"));
    }
}
