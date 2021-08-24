#![feature(str_internals)]
#![feature(vec_into_raw_parts)]

pub mod string_base;
pub mod chars;
mod validation;

pub type str = string_base::StringBase<[u8]>;
pub type String = string_base::StringBase<Vec<u8>>;

#[cfg(test)]
mod tests {
    #[test]
    fn test() {
        let foo: &str = "foo".into();
        let bar: &str = "bar".into();

        let mut foobar = foo.to_owned();
        foobar.push_str(bar);

        println!("{}", foobar);
    }
}
