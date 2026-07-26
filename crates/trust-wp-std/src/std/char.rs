// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable helper traits for `char`.
//!
//! Reference: Creusot `creusot-std/src/std/char.rs`

use crate::logic::Seq;

/// Extra methods for `char`.
pub trait CharExt {
    /// UTF-8 encoding of this character as a logical byte sequence.
    fn to_utf8(self) -> Seq<u8>;
}

impl CharExt for char {
    fn to_utf8(self) -> Seq<u8> {
        let mut buf = [0_u8; 4];
        let encoded = self.encode_utf8(&mut buf);
        Seq::from(encoded.as_bytes().to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_char_to_utf8_ascii() {
        assert_eq!('x'.to_utf8(), Seq::from(vec![b'x']));
    }

    #[test]
    fn test_char_to_utf8_multibyte() {
        assert_eq!('é'.to_utf8(), Seq::from(vec![0xC3, 0xA9]));
    }
}
