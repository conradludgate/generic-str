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
#![feature(const_fn_trait_bound)]

use std::alloc::{Global};

use generic_vec::{ArrayVec, HeapVec};


pub mod string_base;
mod validation;
mod traits;
mod slice_index;
mod convert;

pub use convert::*;

#[allow(non_camel_case_types)]
/// Exactly the same as [`std::str`], except generic
pub type str = string_base::StringBase<[u8]>;

/// Exactly the same as [`std::string::String`], except generic
///
/// ```
/// # use cursed_strings::String;
/// let mut s = String::new();
/// s.push_str("foobar".into());
/// assert_eq!(s, "foobar");
/// ```
pub type String<A = Global> = string_base::StringBase<HeapVec<u8, A>>;

/// Same API as [`String`] but without any re-allocation. Can only hold up to `N` bytes
///
/// ```
/// # use cursed_strings::ArrayString;
/// let mut s = ArrayString::<8>::new();
/// assert_eq!(std::mem::size_of_val(&s), 8 + 8); // 8 bytes of storage, 8 bytes for length
///
/// s.push_str("foo".into());
/// let t = s.clone(); // cloning requires no heap allocations
/// s.push_str("bar".into());
///
/// assert_eq!(t, "foo");
/// assert_eq!(s, "foobar");
/// ```
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
