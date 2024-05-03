//! Issue #114456: `deeply_normalize` tys in `check_tys_might_be_eq`
//@ check-pass
#![feature(adt_const_params)]
#![allow(incomplete_features)]

enum Type {}
trait Trait { type Matrix; }
impl Trait for Type { type Matrix = [usize; 1]; }

struct Walk<const REMAINING: <Type as Trait>::Matrix> {}

impl Walk<{ [0; 1] }> {
    pub const fn new() -> Self {
        Self {}
    }
}

fn main() {
    let _ = Walk::new();
}
