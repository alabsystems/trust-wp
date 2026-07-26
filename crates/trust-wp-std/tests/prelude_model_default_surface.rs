// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[allow(dead_code)]
mod prelude_default_surface {
    use trust_wp_std::prelude::*;

    // `self::Default` proves the prelude re-export resolved in this module,
    // not the standard library prelude.
    #[derive(self::Default)]
    enum Wrapper {
        #[default]
        A(i32, bool),
        B,
    }

    fn typecheck() -> Wrapper {
        Wrapper::default()
    }
}

#[allow(dead_code)]
mod prelude_deep_model_surface {
    use trust_wp_std::prelude::*;

    #[derive(self::DeepModel)]
    struct Wrapper<T: DeepModel>(T, bool);

    #[derive(self::DeepModel)]
    enum Either<T: DeepModel> {
        Left(T),
        Right { ok: bool },
    }

    fn require_deep_model<T: DeepModel>() {}

    fn typecheck() {
        require_deep_model::<i32>();
        let _ = core::mem::size_of::<Wrapper<i32>>();
        let _ = core::mem::size_of::<Either<i32>>();
        let _ = 1i32.deep_model();
    }
}

#[test]
#[allow(clippy::assertions_on_constants)]
fn prelude_resolves_default_and_deep_model() {
    assert!(true);
}
