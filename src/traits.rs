use generic_vec::{raw::Heap, HeapVec};

use crate::string_base::StringBase;
use std::{
    alloc::Allocator,
    borrow::Borrow,
    cmp::Ordering,
    ops::{Index, IndexMut},
    ptr::NonNull,
};

impl<T: ?Sized + std::ops::Deref> std::ops::Deref for StringBase<T> {
    type Target = StringBase<T::Target>;

    fn deref(&self) -> &StringBase<T::Target> {
        unsafe { std::mem::transmute::<&T::Target, &StringBase<T::Target>>(self.storage.deref()) }
    }
}

impl<T: ?Sized + std::ops::DerefMut> std::ops::DerefMut for StringBase<T> {
    fn deref_mut(&mut self) -> &mut StringBase<T::Target> {
        unsafe {
            std::mem::transmute::<&mut T::Target, &mut StringBase<T::Target>>(
                self.storage.deref_mut(),
            )
        }
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
        unsafe {
            std::mem::transmute::<&T::Output, &StringBase<T::Output>>(self.storage.index(index))
        }
    }
}

impl<R, T: ?Sized + IndexMut<R>> IndexMut<R> for StringBase<T> {
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        unsafe {
            std::mem::transmute::<&mut T::Output, &mut StringBase<T::Output>>(
                self.storage.index_mut(index),
            )
        }
    }
}

impl<T: ?Sized> std::fmt::Debug for StringBase<T>
where
    Self: AsRef<StringBase<[u8]>>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: &StringBase<[u8]> = self.as_ref();
        let s: &str = s.as_ref();
        write!(f, "{:?}", s)
    }
}

impl<T: ?Sized> std::fmt::Display for StringBase<T>
where
    Self: AsRef<StringBase<[u8]>>,
{
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
        Self::Owned {
            storage: self.storage.to_owned().into(),
        }
    }
}

impl From<String> for StringBase<HeapVec<u8>> {
    fn from(s: String) -> Self {
        let (ptr, len, capacity) = s.into_raw_parts();
        unsafe {
            Self {
                storage: HeapVec::<u8>::from_raw_parts(
                    len,
                    Heap::<u8>::from_raw_parts(NonNull::new_unchecked(ptr), capacity),
                ),
            }
        }
    }
}

impl From<&str> for StringBase<HeapVec<u8>> {
    fn from(s: &str) -> Self {
        s.to_owned().into()
    }
}

impl From<String> for StringBase<Vec<u8>> {
    fn from(s: String) -> Self {
        let (ptr, length, capacity) = s.into_raw_parts();
        unsafe {
            Self {
                storage: Vec::<u8>::from_raw_parts(ptr, length, capacity),
            }
        }
    }
}

impl From<&mut str> for &mut StringBase<[u8]> {
    fn from(s: &mut str) -> Self {
        unsafe { std::mem::transmute(s) }
    }
}

impl<'a, S: ?Sized + AsRef<[u8]>> From<&'a StringBase<S>> for &'a str {
    fn from(s: &'a StringBase<S>) -> Self {
        unsafe { std::mem::transmute(s.storage.as_ref()) }
    }
}

impl<S: ?Sized, T: ?Sized> PartialEq<StringBase<T>> for StringBase<S>
where
    S: PartialEq<T>,
{
    fn eq(&self, other: &StringBase<T>) -> bool {
        self.storage == other.storage
    }
    fn ne(&self, other: &StringBase<T>) -> bool {
        self.storage != other.storage
    }
}

impl<S: ?Sized + AsRef<[u8]>, T: ?Sized + AsRef<[u8]>> PartialEq<T> for StringBase<S> {
    fn eq(&self, other: &T) -> bool {
        self.storage.as_ref() == other.as_ref()
    }
    fn ne(&self, other: &T) -> bool {
        self.storage.as_ref() != other.as_ref()
    }
}

impl<S: ?Sized + Eq> Eq for StringBase<S> {}

impl<S: ?Sized, T: ?Sized> PartialOrd<StringBase<T>> for StringBase<S>
where
    S: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &StringBase<T>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<S: ?Sized + Ord> Ord for StringBase<S> {
    fn cmp(&self, other: &StringBase<S>) -> Ordering {
        self.storage.cmp(&other.storage)
    }
}
