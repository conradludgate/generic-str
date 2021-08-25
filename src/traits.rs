use generic_vec::HeapVec;

use crate::string_base::StringBase;
use std::{alloc::Allocator, borrow::Borrow, ops::{Index, IndexMut}};

impl<T: std::ops::Deref> std::ops::Deref for StringBase<T> {
    type Target = StringBase<T::Target>;

    fn deref(&self) -> &StringBase<T::Target> {
        unsafe { std::mem::transmute::<&T::Target, &StringBase<T::Target>>(self.storage.deref()) }
    }
}

impl<T: std::ops::DerefMut> std::ops::DerefMut for StringBase<T> {
    fn deref_mut(&mut self) -> &mut StringBase<T::Target> {
        unsafe { std::mem::transmute::<&mut T::Target, &mut StringBase<T::Target>>(self.storage.deref_mut()) }
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

impl<T: ?Sized + AsMut<U>, U: ?Sized> AsMut<StringBase<U>> for StringBase<T> {
    fn as_mut(&mut self) -> &mut StringBase<U> {
        unsafe { std::mem::transmute::<&mut U, &mut StringBase<U>>(self.storage.as_mut()) }
    }
}

impl AsMut<str> for StringBase<[u8]> {
    fn as_mut(&mut self) -> &mut str {
        unsafe { std::str::from_utf8_unchecked_mut(&mut self.storage) }
    }
}

impl<R, T: ?Sized + Index<R>> Index<R> for StringBase<T> {
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

impl<A: Allocator> Borrow<StringBase<[u8]>> for StringBase<HeapVec<u8, A>> {
    fn borrow(&self) -> &StringBase<[u8]> {
        unsafe { std::mem::transmute::<&[u8], &StringBase<[u8]>>(self.storage.borrow()) }
    }
}

impl ToOwned for StringBase<[u8]> {
    type Owned = StringBase<HeapVec<u8>>;

    fn to_owned(&self) -> Self::Owned {
        Self::Owned { storage: self.storage.to_owned().into() }
    }
}

impl From<String> for StringBase<Vec<u8>> {
    fn from(s: String) -> Self {
        let (ptr, length, capacity) = s.into_raw_parts();
        unsafe { Self { storage: Vec::<u8>::from_raw_parts(ptr, length, capacity) } }
    }
}
