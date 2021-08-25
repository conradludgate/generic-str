//! The one and only string type in Rust
//!
//! ```
//! # use cursed_strings::str; use std::ops::Deref;
//! let foo: &str = "foo".into();
//! let expected: &str = "foobar".into();
//!
//! let mut foobar = foo.to_owned();
//! foobar.push_str("bar".into());
//!
//! assert_eq!(foobar.deref(), expected);
//! ```
#![feature(str_internals)]
#![feature(vec_into_raw_parts)]
#![feature(allocator_api)]
#![feature(slice_range)]
#![feature(slice_index_methods)]
#![feature(slice_ptr_get)]
#![feature(slice_ptr_len)]

use std::alloc::{Global};

use generic_vec::{HeapVec};


pub mod string_base;
pub mod chars;
mod validation;
mod traits;
mod slice_index;

#[allow(non_camel_case_types)]
pub type str = string_base::StringBase<[u8]>;
pub type String<A = Global> = string_base::StringBase<HeapVec<u8, A>>;

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use crate::str;

    #[test]
    fn test() {
        let foo: &str = "foo".into();
        let expected: &str = "foobar".into();

        let mut foobar = foo.to_owned();
        foobar.push_str("bar".into());

        assert_eq!(foobar.deref(), expected);
    }
}
