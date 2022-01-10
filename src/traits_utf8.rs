use generic_vec::raw::Storage;

#[cfg(feature = "alloc")]
use generic_vec::HeapVec;
#[cfg(feature = "alloc")]
use std::{
    borrow::Cow,
    ops::{Add, AddAssign},
};

use crate::{string_base::StringBase, OwnedString};
use core::{
    ops::{Index, IndexMut},
    slice::SliceIndex,
};

impl AsRef<str> for StringBase<[u8]> {
    fn as_ref(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(&self.storage) }
    }
}

impl AsMut<str> for StringBase<[u8]> {
    fn as_mut(&mut self) -> &mut str {
        unsafe { core::str::from_utf8_unchecked_mut(&mut self.storage) }
    }
}

impl<I> Index<I> for StringBase<[u8]>
where
    I: SliceIndex<StringBase<[u8]>>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

impl<I> IndexMut<I> for StringBase<[u8]>
where
    I: SliceIndex<StringBase<[u8]>>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

impl<S: ?Sized + Storage<Item = u8>> core::fmt::Debug for OwnedString<u8, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s: &StringBase<[S::Item]> = self.as_ref();
        let s: &str = s.as_ref();
        write!(f, "{:?}", s)
    }
}

impl<S: ?Sized + Storage<Item = u8>> core::fmt::Display for OwnedString<u8, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s: &StringBase<[S::Item]> = self.as_ref();
        let s: &str = s.as_ref();
        write!(f, "{}", s)
    }
}

impl core::fmt::Debug for StringBase<[u8]> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s: &str = self.as_ref();
        write!(f, "{:?}", s)
    }
}

impl core::fmt::Display for StringBase<[u8]> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s: &str = self.as_ref();
        write!(f, "{}", s)
    }
}

#[cfg(feature = "alloc")]
impl From<String> for StringBase<HeapVec<u8>> {
    fn from(s: String) -> Self {
        let (ptr, len, capacity) = s.into_raw_parts();
        unsafe {
            let ptr = std::ptr::slice_from_raw_parts_mut(ptr.cast(), capacity);
            let storage = Box::from_raw(ptr);
            let storage = HeapVec::from_raw_parts(len, storage);
            Self { storage }
        }
    }
}

#[cfg(feature = "alloc")]
impl From<&str> for StringBase<HeapVec<u8>> {
    fn from(s: &str) -> Self {
        s.to_owned().into()
    }
}

impl From<&str> for &StringBase<[u8]> {
    fn from(s: &str) -> Self {
        unsafe { core::mem::transmute(s) }
    }
}

impl From<&mut str> for &mut StringBase<[u8]> {
    fn from(s: &mut str) -> Self {
        unsafe { core::mem::transmute(s) }
    }
}

impl<'a, S: ?Sized + AsRef<[u8]>> From<&'a StringBase<S>> for &'a str {
    fn from(s: &'a StringBase<S>) -> Self {
        unsafe { core::str::from_utf8_unchecked(s.storage.as_ref()) }
    }
}

#[cfg(feature = "alloc")]
impl<'a> Add<&'a crate::str> for Cow<'a, crate::str> {
    type Output = Cow<'a, crate::str>;

    #[inline]
    fn add(mut self, rhs: &'a crate::str) -> Self::Output {
        self += rhs;
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a> AddAssign<&'a crate::str> for Cow<'a, crate::str> {
    fn add_assign(&mut self, rhs: &'a crate::str) {
        if self.is_empty() {
            *self = Cow::Borrowed(rhs)
        } else if !rhs.is_empty() {
            if let Cow::Borrowed(lhs) = *self {
                let mut s = crate::String::with_capacity(lhs.len() + rhs.len());
                s.push_str(lhs);
                *self = Cow::Owned(s);
            }
            self.to_mut().push_str(rhs);
        }
    }
}
