#[cfg(feature = "alloc")]
use std::alloc::{Allocator, Global};
use std::mem::MaybeUninit;

use generic_vec::{
    raw::{Storage, StorageWithCapacity},
    ArrayVec, GenericVec,
};

use crate::{OwnedString, StringBase};

/// UTF-32 Owned String that supports reallocation
///
/// ```
/// # use generic_str::String32;
/// let mut s = String32::new();
/// s.push_str32(&String32::from("foobar"));
/// assert_eq!(s, String32::from("foobar"));
/// ```
#[cfg(feature = "alloc")]
pub type String32<A = Global> = OwnedString<char, Box<[MaybeUninit<char>], A>>;

/// UTF-32 Owned String that has a fixed capacity
///
/// ```
/// # use generic_str::{String32, ArrayString32};
/// let mut s = ArrayString32::<8>::new();
/// assert_eq!(std::mem::size_of_val(&s), 8 * 4 + 8); // 8 chars of storage, 8 bytes for length
///
/// s.push_str32(&String32::from("foo"));
/// let t = s.clone(); // cloning requires no heap allocations
/// s.push_str32(&String32::from("bar"));
///
/// assert_eq!(t, String32::from("foo"));
/// assert_eq!(s, String32::from("foobar"));
/// ```
pub type ArrayString32<const N: usize> = OwnedString<char, [MaybeUninit<char>; N]>;

#[cfg(feature = "alloc")]
impl String32 {
    /// Creates a new empty `String32`.
    ///
    /// Given that the `String32` is empty, this will not allocate any initial
    /// buffer. While that means that this initial operation is very
    /// inexpensive, it may cause excessive allocation later when you add
    /// data. If you have an idea of how much data the `String32` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: String32::with_capacity
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let s = String32::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self::with_storage(Box::default())
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
    /// # use generic_str::String32;
    /// let mut s = String32::with_capacity(10);
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

#[cfg(feature = "alloc")]
impl<A: Allocator> String32<A> {
    pub fn with_alloc(alloc: A) -> Self {
        Self::with_storage(Box::new_uninit_slice_in(0, alloc))
    }
}

impl<const N: usize> ArrayString32<N> {
    /// Creates a new empty `ArrayString`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::ArrayString32;
    /// let s = ArrayString32::<8>::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            storage: ArrayVec::new(),
        }
    }
}

impl<S: ?Sized + Storage<Item = char>> OwnedString<char, S> {
    /// Appends a given string slice onto the end of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::from("foo");
    /// let t = String32::from("bar");
    ///
    /// s.push_str32(&t);
    ///
    /// assert_eq!(s, String32::from("foobar"));
    /// ```
    #[inline]
    pub fn push_str32(&mut self, string: &crate::str32) {
        self.storage.extend_from_slice(&string.storage)
    }

    /// Appends the given [`char`] to the end of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::new();
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!(s, String32::from("123"));
    /// ```
    #[inline]
    pub fn push(&mut self, ch: char) {
        self.storage.push(ch);
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `String` is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::from("foo");
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        self.storage.try_pop()
    }

    /// Shortens this `String` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!(s, String32::from("he"));
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        self.storage.truncate(new_len)
    }

    /// Removes a [`char`] from this `String` at a byte position and returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `String`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::from("foo");
    ///
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// ```
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        self.storage.remove(idx)
    }

    /// Inserts a character into this `String` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::with_capacity(3);
    ///
    /// s.insert(0, 'f');
    /// s.insert(1, 'o');
    /// s.insert(2, 'o');
    ///
    /// assert_eq!(s, String32::from("foo"));
    /// ```
    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char) {
        self.storage.insert(idx, ch);
    }

    /// Returns a mutable reference to the contents of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&['h', 'e', 'l', 'l', 'o'][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, String32::from("olleh"));
    /// ```
    #[inline]
    pub fn as_mut_vec(&mut self) -> &mut GenericVec<S::Item, S> {
        &mut self.storage
    }

    /// Splits the string into two at the given byte index.
    ///
    /// Returns a newly allocated `String`. `self` contains bytes `[0, at)`, and
    /// the returned `String` contains bytes `[at, len)`. `at` must be on the
    /// boundary of a UTF-8 code point.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
    /// code point of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use generic_str::String32;
    /// # fn main() {
    /// let mut hello = String32::from("Hello, World!");
    /// let world: String32 = hello.split_off(7);
    /// assert_eq!(hello, String32::from("Hello, "));
    /// assert_eq!(world, String32::from("World!"));
    /// # }
    /// ```
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off<B: ?Sized + StorageWithCapacity<Item = char>>(
        &mut self,
        at: usize,
    ) -> OwnedString<char, B> {
        let other = self.storage.split_off(at);
        StringBase { storage: other }
    }

    /// Truncates this `String`, removing all contents.
    ///
    /// While this means the `String` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let mut s = String32::from("foo");
    /// let cap = s.capacity();
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(cap, s.capacity());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.storage.clear()
    }

    /// Returns this `String`'s capacity, in bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::String32;
    /// let s = String32::with_capacity(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.capacity()
    }
}
