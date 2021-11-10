use std::slice::SliceIndex;

use crate::StringSlice;

#[allow(non_camel_case_types)]
/// Exactly the same as [`std::str`], except generic
pub type str32 = StringSlice<char>;

impl str32 {
    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not [`char`]s or graphemes. In other words,
    /// it may not be what a human considers the length of the string.
    ///
    /// [`char`]: prim@char
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// assert_eq!(String32::from("foo").len(), 3);
    /// assert_eq!(String32::from("ƒoo").len(), 3); // fancy f!
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.storage.as_ref().len()
    }

    /// Returns `true` if `self` has a length of zero bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let s = String32::from("");
    /// assert!(s.is_empty());
    ///
    /// let s = String32::from("not empty");
    /// assert!(!s.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }

    /// Converts a string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`char`]. This pointer will be pointing to the first byte of the string
    /// slice.
    ///
    /// The caller must ensure that the returned pointer is never written to.
    /// If you need to mutate the contents of the string slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: str::as_mut_ptr
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let s = String32::from("Hello");
    /// let ptr = s.as_ptr();
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *const char {
        self.storage.as_ref() as *const [char] as *const char
    }

    /// Converts a mutable string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`char`]. This pointer will be pointing to the first byte of the string
    /// slice.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut char {
        self.storage.as_mut() as *mut [char] as *mut char
    }

    /// Converts a mutable string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`char`]. This pointer will be pointing to the first byte of the string
    /// slice.
    #[inline]
    pub unsafe fn from_slice(data: &[char]) -> &Self {
        std::mem::transmute(data)
    }

    /// Converts a mutable string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`char`]. This pointer will be pointing to the first byte of the string
    /// slice.
    #[inline]
    pub unsafe fn from_slice_mut(data: &mut [char]) -> &mut Self {
        std::mem::transmute(data)
    }

    /// Returns a subslice of `str`.
    ///
    /// This is the non-panicking alternative to indexing the `str`. Returns
    /// [`None`] whenever equivalent indexing operation would panic.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::{str, String32};
    /// let v = String32::from("🗻∈🌏");
    ///
    /// assert_eq!(v.get(0..2).unwrap().to_owned(), String32::from("🗻∈"));
    ///
    /// // out of bounds
    /// assert!(v.get(..4).is_none());
    /// ```
    #[inline]
    pub fn get<I: SliceIndex<Self>>(&self, i: I) -> Option<&I::Output> {
        i.get(self.as_ref())
    }

    /// Returns a mutable subslice of `str`.
    ///
    /// This is the non-panicking alternative to indexing the `str`. Returns
    /// [`None`] whenever equivalent indexing operation would panic.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::{str, String32};
    /// let mut v = String32::from("hello");
    /// // correct length
    /// assert!(v.get_mut(0..5).is_some());
    /// // out of bounds
    /// assert!(v.get_mut(..42).is_none());
    ///
    /// {
    ///     let s = v.get_mut(0..2);
    ///     let s = s.map(|s| {
    ///         s.make_ascii_uppercase();
    ///         &*s
    ///     });
    /// }
    /// assert_eq!(v, String32::from("HEllo"));
    /// ```
    #[inline]
    pub fn get_mut<I: SliceIndex<Self>>(&mut self, i: I) -> Option<&mut I::Output> {
        i.get_mut(self.as_mut())
    }

    /// Returns an unchecked subslice of `str`.
    ///
    /// This is the unchecked alternative to indexing the `str`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible that these preconditions are
    /// satisfied:
    ///
    /// * The starting index must not exceed the ending index;
    /// * Indexes must be within bounds of the original slice;
    /// * Indexes must lie on UTF-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `str` type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let v = "🗻∈🌏";
    /// unsafe {
    ///     assert_eq!(v.get_unchecked(0..4), "🗻");
    ///     assert_eq!(v.get_unchecked(4..7), "∈");
    ///     assert_eq!(v.get_unchecked(7..11), "🌏");
    /// }
    /// ```
    #[inline]
    pub unsafe fn get_unchecked<I: SliceIndex<Self>>(&self, i: I) -> &I::Output {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked`;
        // the slice is dereferencable because `self` is a safe reference.
        // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
        &*i.get_unchecked(self)
    }

    /// Returns a mutable, unchecked subslice of `str`.
    ///
    /// This is the unchecked alternative to indexing the `str`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible that these preconditions are
    /// satisfied:
    ///
    /// * The starting index must not exceed the ending index;
    /// * Indexes must be within bounds of the original slice;
    /// * Indexes must lie on UTF-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `str` type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let mut v = String32::from("🗻∈🌏");
    /// unsafe {
    ///     assert_eq!(*v.get_unchecked_mut(0..2), String32::from("🗻∈"));
    /// }
    /// ```
    #[inline]
    pub unsafe fn get_unchecked_mut<I: SliceIndex<Self>>(&mut self, i: I) -> &mut I::Output {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked_mut`;
        // the slice is dereferencable because `self` is a safe reference.
        // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
        &mut *i.get_unchecked_mut(self)
    }

    /// Divide one string slice into two at an index.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`split_at_mut`]
    /// method.
    ///
    /// [`split_at_mut`]: str32::split_at_mut
    ///
    /// # Panics
    ///
    /// Panics if `mid` is past the end of the last code point of the string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let s = String32::from("Per Martin-Löf");
    ///
    /// let (first, last) = s.split_at(3);
    ///
    /// assert_eq!(first.to_owned(), String32::from("Per"));
    /// assert_eq!(last.to_owned(), String32::from(" Martin-Löf"));
    /// ```
    #[inline]
    pub fn split_at(&self, mid: usize) -> (&Self, &Self) {
        if mid <= self.len() {
            unsafe {
                (
                    self.get_unchecked(0..mid),
                    self.get_unchecked(mid..self.len()),
                )
            }
        } else {
            panic!("char index {} is out of bounds of `{}`", mid, self);
        }
    }

    /// Divide one mutable string slice into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a UTF-8 code point.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get immutable string slices instead, see the [`split_at`] method.
    ///
    /// [`split_at`]: str32::split_at
    ///
    /// # Panics
    ///
    /// Panics if `mid` is not on a UTF-8 code point boundary, or if it is
    /// past the end of the last code point of the string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let mut s = String32::from("Per Martin-Löf");
    /// {
    ///     let (first, last) = s.split_at_mut(3);
    ///     first.make_ascii_uppercase();
    ///     assert_eq!(first.to_owned(), String32::from("PER"));
    ///     assert_eq!(last.to_owned(), String32::from(" Martin-Löf"));
    /// }
    /// assert_eq!(s, String32::from("PER Martin-Löf"));
    /// ```
    #[inline]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        // is_char_boundary checks that the index is in [0, .len()]
        if mid < self.len() {
            let len = self.len();
            let ptr = self.as_mut_ptr();
            // SAFETY: just checked that `mid` is on a char boundary.
            unsafe {
                (
                    Self::from_slice_mut(std::slice::from_raw_parts_mut(ptr, mid)),
                    Self::from_slice_mut(std::slice::from_raw_parts_mut(ptr.add(mid), len - mid)),
                )
            }
        } else {
            panic!("char index {} is out of bounds of `{}`", mid, self);
        }
    }

    /// Converts this string to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new uppercased value without modifying the existing one, use
    /// [`to_ascii_uppercase()`].
    ///
    /// [`to_ascii_uppercase()`]: #method.to_ascii_uppercase
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let mut s = String32::from("Grüße, Jürgen ❤");
    ///
    /// s.make_ascii_uppercase();
    ///
    /// assert_eq!(s, String32::from("GRüßE, JüRGEN ❤"));
    /// ```
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        self.storage.iter_mut().for_each(char::make_ascii_uppercase)
    }

    /// Converts this string to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new lowercased value without modifying the existing one, use
    /// [`to_ascii_lowercase()`].
    ///
    /// [`to_ascii_lowercase()`]: #method.to_ascii_lowercase
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::String32;
    /// let mut s = String32::from("GRÜßE, JÜRGEN ❤");
    ///
    /// s.make_ascii_lowercase();
    ///
    /// assert_eq!(s, String32::from("grÜße, jÜrgen ❤"));
    /// ```
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        self.storage.iter_mut().for_each(char::make_ascii_lowercase)
    }
}
