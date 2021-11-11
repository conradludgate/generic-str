use generic_vec::{raw::Storage, GenericVec};

#[cfg(feature = "alloc")]
use generic_vec::HeapVec;
#[cfg(feature = "alloc")]
use std::{
    borrow::Cow,
    iter::FromIterator,
    ops::{Add, AddAssign},
};

use crate::string_base::StringBase;
use core::{
    ops::{Index, IndexMut},
    slice::SliceIndex,
};

impl<I> Index<I> for crate::str32
where
    I: SliceIndex<crate::str32>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

impl<I> IndexMut<I> for crate::str32
where
    I: SliceIndex<crate::str32>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

#[cfg(feature = "alloc")]
impl<S: ?Sized + Storage<char>> std::fmt::Debug for StringBase<GenericVec<char, S>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.as_ref().storage.iter().collect();
        write!(f, "{:?}", s)
    }
}

#[cfg(feature = "alloc")]
impl<S: ?Sized + Storage<char>> std::fmt::Display for StringBase<GenericVec<char, S>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.as_ref().storage.iter().collect();
        write!(f, "{}", s)
    }
}

#[cfg(feature = "alloc")]
impl std::fmt::Debug for crate::str32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.storage.iter().collect();
        write!(f, "{:?}", s)
    }
}

#[cfg(feature = "alloc")]
impl std::fmt::Display for crate::str32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = self.storage.iter().collect();
        write!(f, "{}", s)
    }
}

#[cfg(feature = "alloc")]
impl From<String> for crate::String32 {
    fn from(s: String) -> Self {
        s.chars().collect()
    }
}

#[cfg(feature = "alloc")]
impl FromIterator<char> for crate::String32 {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut new = Self::new();
        iter.into_iter().for_each(|c| new.push(c));
        new
    }
}

#[cfg(feature = "alloc")]
impl From<&str> for StringBase<HeapVec<char>> {
    fn from(s: &str) -> Self {
        s.to_owned().into()
    }
}

impl From<&str> for &crate::str32 {
    fn from(s: &str) -> Self {
        unsafe { core::mem::transmute(s) }
    }
}

impl From<&mut str> for &mut crate::str32 {
    fn from(s: &mut str) -> Self {
        unsafe { core::mem::transmute(s) }
    }
}

impl<S: ?Sized + Storage<char>, T: ?Sized + AsRef<[char]>> PartialEq<T>
    for StringBase<GenericVec<char, S>>
{
    fn eq(&self, other: &T) -> bool {
        self.storage.as_ref() == other.as_ref()
    }
}

impl<T: ?Sized + AsRef<[char]>> PartialEq<T> for crate::str32 {
    fn eq(&self, other: &T) -> bool {
        self.storage.as_ref() == other.as_ref()
    }
}

#[cfg(feature = "alloc")]
impl<'a> Add<&'a crate::str32> for Cow<'a, crate::str32> {
    type Output = Cow<'a, crate::str32>;

    #[inline]
    fn add(mut self, rhs: &'a crate::str32) -> Self::Output {
        self += rhs;
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a> AddAssign<&'a crate::str32> for Cow<'a, crate::str32> {
    fn add_assign(&mut self, rhs: &'a crate::str32) {
        if self.is_empty() {
            *self = Cow::Borrowed(rhs)
        } else if !rhs.is_empty() {
            if let Cow::Borrowed(lhs) = *self {
                let mut s = crate::String32::with_capacity(lhs.len() + rhs.len());
                s.push_str32(lhs);
                *self = Cow::Owned(s);
            }
            self.to_mut().push_str32(rhs);
        }
    }
}
