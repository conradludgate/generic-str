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

mod convert;
mod owned_utf8;
mod slice_index;
mod slice_utf8;
mod string_base;
mod traits;
mod validation;

pub use convert::*;
pub use owned_utf8::FromUtf8Error;
pub use string_base::*;

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
