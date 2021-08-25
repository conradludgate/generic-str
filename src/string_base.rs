use std::alloc::{Allocator, Global};

use generic_vec::{raw::Heap, ArrayVec, HeapVec};

#[derive(Default, Copy, Clone)]
#[repr(transparent)]
pub struct StringBase<S: ?Sized> {
    pub(crate) storage: S,
}

#[allow(non_camel_case_types)]
/// Exactly the same as [`std::str`], except generic
pub type str = StringBase<[u8]>;

/// Exactly the same as [`std::string::String`], except generic
///
/// ```
/// # use cursed_strings::String;
/// let mut s = String::new();
/// s.push_str("foobar".into());
/// assert_eq!(s, "foobar");
/// ```
pub type String<A = Global> = StringBase<HeapVec<u8, A>>;

/// Same API as [`String`] but without any re-allocation. Can only hold up to `N` bytes
///
/// ```
/// # use cursed_strings::ArrayString;
/// let mut s = ArrayString::<8>::new();
/// assert_eq!(std::mem::size_of_val(&s), 8 + 8); // 8 bytes of storage, 8 bytes for length
///
/// s.push_str("foo".into());
/// let t = s.clone(); // cloning requires no heap allocations
/// s.push_str("bar".into());
///
/// assert_eq!(t, "foo");
/// assert_eq!(s, "foobar");
/// ```
pub type ArrayString<const N: usize> = StringBase<ArrayVec<u8, N>>;

impl crate::String {
    /// Creates a new empty `String`.
    ///
    /// Given that the `String` is empty, this will not allocate any initial
    /// buffer. While that means that this initial operation is very
    /// inexpensive, it may cause excessive allocation later when you add
    /// data. If you have an idea of how much data the `String` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: StringBase::with_capacity
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::String;
    /// let s = String::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self::with_storage(Heap::new())
    }

    /// Creates a new empty `String` with a particular capacity.
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
    pub fn with_capacity(capacity: usize) -> Self {
        Self::new_with_capacity(capacity)
    }
}

impl<A: Allocator> crate::String<A> {
    pub fn with_alloc(alloc: A) -> Self {
        Self::with_storage(Heap::with_alloc(alloc))
    }
}

impl<const N: usize> crate::ArrayString<N> {
    /// Creates a new empty `ArrayString`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::ArrayString;
    /// let s = ArrayString::<8>::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            storage: ArrayVec::new(),
        }
    }
}
