// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod tuple_struct_surface {
    use creusot_std::prelude::Default;

    #[derive(Default)]
    struct Tuple(pub i32, pub bool);

    #[test]
    fn tuple_struct_default_uses_creusot_surface() {
        let value = Tuple::default();
        assert_eq!(value.0, 0);
        assert!(!value.1);
    }
}

mod unit_struct_surface {
    use creusot_std::prelude::Default;

    #[derive(Default)]
    struct Unit;

    #[test]
    #[allow(clippy::default_constructed_unit_structs)]
    fn unit_struct_default_uses_unit_constructor() {
        let _value = Unit::default();
    }
}

mod named_struct_surface {
    use creusot_std::prelude::Default;

    #[derive(Default)]
    struct Named<T> {
        x: i32,
        y: T,
    }

    #[test]
    fn named_struct_default_uses_creusot_surface() {
        let value = Named::<bool>::default();
        assert_eq!(value.x, 0);
        assert!(!value.y);
    }
}

mod tuple_enum_surface {
    use creusot_std::prelude::Default;

    #[derive(Default)]
    enum TupleEnum {
        #[default]
        A(i32, bool),
        B,
    }

    #[test]
    fn tuple_enum_default_variant_supports_non_unit_fields() {
        assert!(matches!(TupleEnum::B, TupleEnum::B));
        match TupleEnum::default() {
            TupleEnum::A(x, y) => {
                assert_eq!(x, 0);
                assert!(!y);
            }
            TupleEnum::B => panic!("expected tuple default variant"),
        }
    }
}

mod unit_enum_surface {
    use creusot_std::prelude::Default;

    #[derive(Default)]
    enum UnitEnum {
        A,
        #[default]
        B,
    }

    #[test]
    fn unit_enum_default_variant_uses_unit_constructor() {
        assert!(matches!(UnitEnum::A, UnitEnum::A));
        assert!(matches!(UnitEnum::default(), UnitEnum::B));
    }
}

mod named_enum_surface {
    use creusot_std::prelude::Default;

    #[derive(Default)]
    enum NamedEnum<T, U> {
        #[default]
        A {
            x: T,
            y: U,
        },
        B,
    }

    #[test]
    fn named_enum_default_variant_supports_named_fields() {
        assert!(matches!(NamedEnum::<i32, bool>::B, NamedEnum::B));
        match NamedEnum::<i32, bool>::default() {
            NamedEnum::A { x, y } => {
                assert_eq!(x, 0);
                assert!(!y);
            }
            NamedEnum::B => panic!("expected named default variant"),
        }
    }
}
