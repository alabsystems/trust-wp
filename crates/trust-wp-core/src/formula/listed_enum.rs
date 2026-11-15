// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `listed_enum!`: a fieldless enum together with the list of its variants.

/// Define a fieldless enum and `pub const ALL: &[Self]`, every variant in
/// declaration order. The list is written by the macro from the variants
/// themselves, so a variant cannot be added without it: a generated oracle
/// that counts its cases over `ALL` finds a new variant with no case.
macro_rules! listed_enum {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$variant_meta:meta])*
                $variant:ident
            ),* $(,)?
        }
    ) => {
        $(#[$meta])*
        $vis enum $name {
            $(
                $(#[$variant_meta])*
                $variant
            ),*
        }

        impl $name {
            /// Every variant, in declaration order.
            pub const ALL: &'static [Self] = &[$(Self::$variant),*];
        }
    };
}

pub(crate) use listed_enum;
