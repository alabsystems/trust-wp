// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[allow(dead_code)]
mod cloned_surface {
    use trust_wp_std::prelude::*;

    fn typecheck(data: &[i32]) {
        let iter = data.iter().copied();
        let _: std::slice::Iter<'_, i32> = iter.iter();
    }
}

#[allow(dead_code)]
mod copied_surface {
    use trust_wp_std::prelude::*;

    fn typecheck(data: &[i32]) {
        let iter = data.iter().copied();
        let _: std::slice::Iter<'_, i32> = iter.iter();
    }
}

#[allow(dead_code)]
mod fuse_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..3).fuse();
        let _: std::ops::Range<i32> = iter.iter();
    }
}

#[allow(dead_code)]
mod take_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).take(3);
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).take(3);
        let _: usize = iter.n();

        let mut iter = (0..5).take(3);
        let _: &mut std::ops::Range<i32> = iter.iter_mut();
    }
}

#[allow(dead_code)]
mod rev_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = vec![1i32, 2, 3].into_iter().rev();
        let _: std::vec::IntoIter<i32> = iter.iter();
    }
}

#[allow(dead_code)]
mod skip_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).skip(3);
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).skip(3);
        let _: usize = iter.n();
    }
}

#[allow(dead_code)]
mod enumerate_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).enumerate();
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).enumerate();
        let _: usize = iter.n();
    }
}

#[allow(dead_code)]
mod zip_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..3).zip(3..6);
        let _: std::ops::Range<i32> = iter.itera();

        let iter = (0..3).zip(3..6);
        let _: std::ops::Range<i32> = iter.iterb();
    }
}

#[allow(dead_code)]
mod map_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).map(|x| x * 2);
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).map(|x| x * 2);
        let _ = iter.func();
    }
}

#[allow(dead_code)]
mod filter_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).filter(|x| *x > 2);
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).filter(|x| *x > 2);
        let _ = iter.func();
    }
}

#[allow(dead_code)]
mod filter_iterator_spec_surface {
    use trust_wp_std::prelude::*;

    fn require_iterator_spec<I: IteratorSpec>(_iter: I) {}

    fn typecheck() {
        let iter = vec![1_i32, 2, 3].into_iter().filter(|x| *x > 1);
        require_iterator_spec(iter);
    }
}

#[allow(dead_code)]
mod iterator_spec_mut_ref_surface {
    use trust_wp_std::prelude::*;

    fn require_iterator_spec<I: IteratorSpec>(_iter: I) {}

    fn typecheck() {
        let mut iter = vec![1_i32, 2, 3].into_iter();
        require_iterator_spec(&mut iter);
    }
}

#[allow(dead_code, clippy::unnecessary_filter_map)]
mod filter_map_surface {
    use trust_wp_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).filter_map(|x| if x > 2 { Some(x) } else { None });
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).filter_map(|x| if x > 2 { Some(x) } else { None });
        let _ = iter.func();
    }
}

#[test]
#[allow(clippy::assertions_on_constants)]
fn prelude_reexports_iterator_adapter_ext_traits() {
    assert!(true);
}
