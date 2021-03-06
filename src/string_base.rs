use core::cmp::Ordering;

use generic_vec::{
    raw::{Storage, StorageWithCapacity},
    GenericVec,
};

#[cfg(feature = "alloc")]
use generic_vec::HeapVec;
#[cfg(feature = "alloc")]
use std::{alloc::Allocator, borrow::Borrow};

#[derive(Default, Copy, Clone)]
#[repr(transparent)]
pub struct StringBase<S: ?Sized> {
    pub(crate) storage: S,
}

impl<S: StorageWithCapacity> StringBase<GenericVec<S::Item, S>> {
    #[inline]
    pub fn new_with_capacity(capacity: usize) -> Self {
        Self::with_storage(S::with_capacity(capacity))
    }
}

pub type OwnedString<T, S> = StringBase<GenericVec<T, S>>;
pub type StringSlice<U> = StringBase<[U]>;

impl<S: ?Sized + Storage> StringBase<GenericVec<S::Item, S>> {
    /// Creates a new empty `String` with a particular storage backend.
    ///
    /// `String`s have an internal buffer to hold their data. The capacity is
    /// the length of that buffer, and can be queried with the [`capacity`]
    /// method. This method creates an empty `String`, but one with an initial
    /// buffer that can hold `capacity` bytes. This is useful when you may be
    /// appending a bunch of data to the `String`, reducing the number of
    /// reallocations it needs to do.
    ///
    /// [`capacity`]: StringBase::capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: StringBase::new
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String;
    /// let mut s = String::with_capacity(10);
    ///
    /// // The String contains no chars, even though it has capacity for more
    /// assert_eq!(s.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// let cap = s.capacity();
    /// for _ in 0..10 {
    ///     s.push('a');
    /// }
    ///
    /// assert_eq!(s.capacity(), cap);
    ///
    /// // ...but this may make the string reallocate
    /// s.push('a');
    /// ```
    #[inline]
    pub fn with_storage(storage: S) -> Self
    where
        S: Sized,
    {
        StringBase {
            storage: GenericVec::with_storage(storage),
        }
    }
}

impl<T: ?Sized + core::ops::Deref> core::ops::Deref for StringBase<T> {
    type Target = StringBase<T::Target>;

    fn deref(&self) -> &StringBase<T::Target> {
        unsafe { core::mem::transmute::<&T::Target, &StringBase<T::Target>>(self.storage.deref()) }
    }
}

impl<T: ?Sized + core::ops::DerefMut> core::ops::DerefMut for StringBase<T> {
    fn deref_mut(&mut self) -> &mut StringBase<T::Target> {
        unsafe {
            core::mem::transmute::<&mut T::Target, &mut StringBase<T::Target>>(
                self.storage.deref_mut(),
            )
        }
    }
}

impl<T: ?Sized + AsRef<U>, U: ?Sized> AsRef<StringBase<U>> for StringBase<T> {
    fn as_ref(&self) -> &StringBase<U> {
        unsafe { core::mem::transmute::<&U, &StringBase<U>>(self.storage.as_ref()) }
    }
}

impl<T: ?Sized + AsMut<U>, U: ?Sized> AsMut<StringBase<U>> for StringBase<T> {
    fn as_mut(&mut self) -> &mut StringBase<U> {
        unsafe { core::mem::transmute::<&mut U, &mut StringBase<U>>(self.storage.as_mut()) }
    }
}

#[cfg(feature = "alloc")]
impl<T, A: Allocator> Borrow<StringBase<[T]>> for StringBase<HeapVec<T, A>> {
    fn borrow(&self) -> &StringBase<[T]> {
        unsafe { std::mem::transmute::<&[T], &StringBase<[T]>>(self.storage.borrow()) }
    }
}

#[cfg(feature = "alloc")]
impl<T: Clone> ToOwned for StringBase<[T]> {
    type Owned = StringBase<HeapVec<T>>;

    fn to_owned(&self) -> Self::Owned {
        Self::Owned {
            storage: self.storage.to_owned().into(),
        }
    }
}

impl<S: ?Sized + Storage, T: ?Sized + Storage> PartialEq<OwnedString<T::Item, T>>
    for StringBase<GenericVec<S::Item, S>>
where
    GenericVec<S::Item, S>: PartialEq<GenericVec<T::Item, T>>,
{
    fn eq(&self, other: &OwnedString<T::Item, T>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<S: ?Sized + Storage> PartialEq<OwnedString<S::Item, S>> for StringSlice<S::Item>
where
    S::Item: PartialEq,
{
    fn eq(&self, other: &OwnedString<S::Item, S>) -> bool {
        other.storage.eq(&self.storage)
    }
}

impl<S: ?Sized + Storage> PartialEq<OwnedString<S::Item, S>> for &StringSlice<S::Item>
where
    S::Item: PartialEq,
{
    fn eq(&self, other: &OwnedString<S::Item, S>) -> bool {
        other.storage.eq(&self.storage)
    }
}

impl<S: ?Sized + Storage> PartialEq<StringSlice<S::Item>> for OwnedString<S::Item, S>
where
    S::Item: PartialEq,
{
    fn eq(&self, other: &StringSlice<S::Item>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<S: ?Sized + Storage> PartialEq<&StringSlice<S::Item>> for OwnedString<S::Item, S>
where
    S::Item: PartialEq,
{
    fn eq(&self, other: &&StringSlice<S::Item>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<U: PartialEq> PartialEq<StringSlice<U>> for StringSlice<U> {
    fn eq(&self, other: &StringSlice<U>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<S: ?Sized + Storage> Eq for OwnedString<S::Item, S> where S::Item: Eq {}
impl<U: Eq> Eq for StringSlice<U> {}

impl<S: ?Sized + Storage, T: ?Sized + Storage> PartialOrd<OwnedString<T::Item, T>>
    for OwnedString<S::Item, S>
where
    GenericVec<S::Item, S>: PartialOrd<GenericVec<T::Item, T>>,
{
    fn partial_cmp(&self, other: &OwnedString<T::Item, T>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<S: ?Sized + Storage> PartialOrd<OwnedString<S::Item, S>> for StringSlice<S::Item>
where
    S::Item: PartialOrd,
{
    fn partial_cmp(&self, other: &OwnedString<S::Item, S>) -> Option<Ordering> {
        other.storage.partial_cmp(&self.storage)
    }
}

impl<S: ?Sized + Storage> PartialOrd<OwnedString<S::Item, S>> for &StringSlice<S::Item>
where
    S::Item: PartialOrd,
{
    fn partial_cmp(&self, other: &OwnedString<S::Item, S>) -> Option<Ordering> {
        other.storage.partial_cmp(&self.storage)
    }
}

impl<S: ?Sized + Storage> PartialOrd<StringSlice<S::Item>> for OwnedString<S::Item, S>
where
    S::Item: PartialOrd,
{
    fn partial_cmp(&self, other: &StringSlice<S::Item>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<S: ?Sized + Storage> PartialOrd<&StringSlice<S::Item>> for OwnedString<S::Item, S>
where
    S::Item: PartialOrd,
{
    fn partial_cmp(&self, other: &&StringSlice<S::Item>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<U: PartialOrd> PartialOrd<StringSlice<U>> for StringSlice<U> {
    fn partial_cmp(&self, other: &StringSlice<U>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<S: ?Sized + Storage> Ord for OwnedString<S::Item, S>
where
    S::Item: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.cmp(&other.storage)
    }
}
impl<U: Ord> Ord for StringSlice<U> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.cmp(&other.storage)
    }
}
