use std::{borrow::Borrow, ops::{Index, IndexMut}};

use crate::chars::{CharIndices, Chars};

#[derive(Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct StringBase<S: ?Sized> {
    storage: S,
}

impl<T: std::ops::Deref> std::ops::Deref for StringBase<T> {
    type Target = StringBase<T::Target>;

    fn deref(&self) -> &StringBase<T::Target> {
        unsafe { std::mem::transmute::<&T::Target, &StringBase<T::Target>>(self.storage.deref()) }
    }
}

impl<T: ?Sized + AsRef<U>, U: ?Sized> AsRef<StringBase<U>> for StringBase<T> {
    fn as_ref(&self) -> &StringBase<U> {
        unsafe { std::mem::transmute::<&U, &StringBase<U>>(self.storage.as_ref()) }
    }
}

impl AsRef<str> for StringBase<[u8]> {
    fn as_ref(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.storage) }
    }
}

impl<T> StringBase<T> {
    pub fn new() -> Self where Self: Default {
        Self::default()
    }
}

impl<R, T: Index<R>> Index<R> for StringBase<T> {
    type Output = StringBase<T::Output>;

    fn index(&self, index: R) -> &Self::Output {
        unsafe { std::mem::transmute::<&T::Output, &StringBase<T::Output>>(self.storage.index(index)) }
    }
}

impl<R, T: IndexMut<R>> IndexMut<R> for StringBase<T> {
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        unsafe { std::mem::transmute::<&mut T::Output, &mut StringBase<T::Output>>(self.storage.index_mut(index)) }
    }
}

impl<T: ?Sized + AsRef<[u8]>> StringBase<T> {
    pub fn chars(&self) -> Chars<'_> {
        Chars { iter: self.storage.as_ref().into_iter() }
    }
    pub fn char_indices(&self) -> CharIndices<'_> {
        CharIndices { front_offset: 0, iter: self.chars() }
    }
}

impl<T: ?Sized> std::fmt::Debug for StringBase<T> where Self: AsRef<StringBase<[u8]>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: &StringBase<[u8]> = self.as_ref();
        let s: &str = s.as_ref();
        write!(f, "{:?}", s)
    }
}

impl<T: ?Sized> std::fmt::Display for StringBase<T> where Self: AsRef<StringBase<[u8]>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: &StringBase<[u8]> = self.as_ref();
        let s: &str = s.as_ref();
        write!(f, "{}", s)
    }
}

impl Borrow<StringBase<[u8]>> for StringBase<Vec<u8>> {
    fn borrow(&self) -> &StringBase<[u8]> {
        unsafe { std::mem::transmute::<&[u8], &StringBase<[u8]>>(self.storage.borrow()) }
    }
}

impl ToOwned for StringBase<[u8]> {
    type Owned = StringBase<Vec<u8>>;

    fn to_owned(&self) -> Self::Owned {
        Self::Owned { storage: self.storage.to_owned() }
    }
}

impl StringBase<Vec<u8>> {
    pub fn push_str(&mut self, string: &StringBase<[u8]>) {
        self.storage.extend_from_slice(&string.storage)
    }
}

impl From<String> for StringBase<Vec<u8>> {
    fn from(s: String) -> Self {
        let (ptr, length, capacity) = s.into_raw_parts();
        unsafe { Self { storage: Vec::<u8>::from_raw_parts(ptr, length, capacity) } }
    }
}

impl From<&str> for &StringBase<[u8]> {
    fn from(s: &str) -> Self {
        unsafe { std::mem::transmute(s) }
    }
}
