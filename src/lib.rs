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


pub mod string_base;
pub mod chars;
mod validation;

pub type str = string_base::StringBase<[u8]>;
pub type String = string_base::StringBase<Vec<u8>>;

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
