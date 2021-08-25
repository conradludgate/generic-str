//! The one and only string type in Rust
//!
//! ```
//! # use cursed_strings::str;
//! let foo: &str = "foo".into();
//! let expected: &str = "foobar".into();
//!
//! let mut foobar = foo.to_owned();
//! foobar.push_str("bar".into());
//!
//! assert_eq!(foobar, *expected);
//! ```
#![feature(str_internals)]
#![feature(vec_into_raw_parts)]
#![feature(allocator_api)]
#![feature(slice_range)]
#![feature(slice_index_methods)]
#![feature(slice_ptr_get)]
#![feature(slice_ptr_len)]
#![feature(const_mut_refs)]

use std::alloc::{Global};

use generic_vec::{ArrayVec, HeapVec};


pub mod string_base;
mod validation;
mod traits;
mod slice_index;
mod convert;

pub use convert::*;

#[allow(non_camel_case_types)]
pub type str = string_base::StringBase<[u8]>;
pub type String<A = Global> = string_base::StringBase<HeapVec<u8, A>>;
pub type ArrayString<const N: usize> = string_base::StringBase<ArrayVec<u8, N>>;

#[cfg(test)]
mod tests {
    use crate::str;

    #[test]
    fn test() {
        let foo: &str = "foo".into();
        let expected: &str = "foobar".into();

        let mut foobar = foo.to_owned();
        foobar.push_str("bar".into());

        assert_eq!(foobar, *expected);
    }
}
