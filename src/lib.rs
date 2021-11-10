//! The one and only string type in Rust
//!
//! ```
//! # use generic_str::str;
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
#![feature(unicode_internals)]

mod convert;
mod owned_utf32;
mod owned_utf8;
mod slice_utf32;
mod slice_utf32_index;
mod slice_utf8;
mod slice_utf8_index;
mod string_base;
mod traits_utf32;
mod traits_utf8;
mod validation;

pub use convert::*;
pub use owned_utf32::*;
pub use owned_utf8::*;
pub use slice_utf32::*;
pub use slice_utf8::*;
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
