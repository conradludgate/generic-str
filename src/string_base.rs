use std::{alloc::Allocator, borrow::Borrow, cmp::Ordering};

use generic_vec::{
    raw::{Storage, StorageWithCapacity},
    GenericVec, HeapVec,
};

#[derive(Default, Copy, Clone)]
#[repr(transparent)]
pub struct StringBase<S: ?Sized> {
    pub(crate) storage: S,
}

impl<S: StorageWithCapacity<T>, T> StringBase<GenericVec<T, S>> {
    #[inline]
    pub fn new_with_capacity(capacity: usize) -> Self {
        Self::with_storage(S::with_capacity(capacity))
    }
}

pub type OwnedString<U, S> = StringBase<GenericVec<U, S>>;
pub type StringSlice<U> = StringBase<[U]>;

impl<S: ?Sized + Storage<T>, T> StringBase<GenericVec<T, S>> {
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
    /// # use cursed_strings::String;
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
    pub const fn with_storage(storage: S) -> Self
    where
        S: Sized,
    {
        StringBase {
            storage: GenericVec::with_storage(storage),
        }
    }
}

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

impl<T: ?Sized + AsMut<U>, U: ?Sized> AsMut<StringBase<U>> for StringBase<T> {
    fn as_mut(&mut self) -> &mut StringBase<U> {
        unsafe { std::mem::transmute::<&mut U, &mut StringBase<U>>(self.storage.as_mut()) }
    }
}

impl<T, A: Allocator> Borrow<StringBase<[T]>> for StringBase<HeapVec<T, A>> {
    fn borrow(&self) -> &StringBase<[T]> {
        unsafe { std::mem::transmute::<&[T], &StringBase<[T]>>(self.storage.borrow()) }
    }
}

impl<T: Clone> ToOwned for StringBase<[T]> {
    type Owned = StringBase<HeapVec<T>>;

    fn to_owned(&self) -> Self::Owned {
        Self::Owned {
            storage: self.storage.to_owned().into(),
        }
    }
}

impl<S: ?Sized + Storage<U>, T: ?Sized + Storage<U>, U> PartialEq<OwnedString<U, T>>
    for StringBase<GenericVec<U, S>>
where
    GenericVec<U, S>: PartialEq<GenericVec<U, T>>,
{
    fn eq(&self, other: &OwnedString<U, T>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialEq> PartialEq<OwnedString<U, S>> for StringSlice<U> {
    fn eq(&self, other: &OwnedString<U, S>) -> bool {
        other.storage.eq(&self.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialEq> PartialEq<OwnedString<U, S>> for &StringSlice<U> {
    fn eq(&self, other: &OwnedString<U, S>) -> bool {
        other.storage.eq(&self.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialEq> PartialEq<StringSlice<U>> for OwnedString<U, S> {
    fn eq(&self, other: &StringSlice<U>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialEq> PartialEq<&StringSlice<U>> for OwnedString<U, S> {
    fn eq(&self, other: &&StringSlice<U>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<U: PartialEq> PartialEq<StringSlice<U>> for StringSlice<U> {
    fn eq(&self, other: &StringSlice<U>) -> bool {
        self.storage.eq(&other.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: Eq> Eq for OwnedString<U, S> {}
impl<U: Eq> Eq for StringSlice<U> {}

impl<S: ?Sized + Storage<U>, T: ?Sized + Storage<U>, U> PartialOrd<OwnedString<U, T>>
    for StringBase<GenericVec<U, S>>
where
    GenericVec<U, S>: PartialOrd<GenericVec<U, T>>,
{
    fn partial_cmp(&self, other: &OwnedString<U, T>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialOrd> PartialOrd<OwnedString<U, S>> for StringSlice<U> {
    fn partial_cmp(&self, other: &OwnedString<U, S>) -> Option<Ordering> {
        other.storage.partial_cmp(&self.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialOrd> PartialOrd<OwnedString<U, S>> for &StringSlice<U> {
    fn partial_cmp(&self, other: &OwnedString<U, S>) -> Option<Ordering> {
        other.storage.partial_cmp(&self.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialOrd> PartialOrd<StringSlice<U>> for OwnedString<U, S> {
    fn partial_cmp(&self, other: &StringSlice<U>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: PartialOrd> PartialOrd<&StringSlice<U>> for OwnedString<U, S> {
    fn partial_cmp(&self, other: &&StringSlice<U>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<U: PartialOrd> PartialOrd<StringSlice<U>> for StringSlice<U> {
    fn partial_cmp(&self, other: &StringSlice<U>) -> Option<Ordering> {
        self.storage.partial_cmp(&other.storage)
    }
}

impl<S: ?Sized + Storage<U>, U: Ord> Ord for OwnedString<U, S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.cmp(&other.storage)
    }
}
impl<U: Ord> Ord for StringSlice<U> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.cmp(&other.storage)
    }
}
