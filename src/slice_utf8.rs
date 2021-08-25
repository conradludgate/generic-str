use std::{
    slice::SliceIndex,
    str::{Bytes, CharIndices, Chars},
};

use crate::{
    from_utf8_unchecked_mut, string_base::StringBase, validation::truncate_to_char_boundary,
};

impl<S: ?Sized + AsRef<[u8]>> StringBase<S> {
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
    /// # use cursed_strings::str;
    /// let len = <&str>::from("foo").len();
    /// assert_eq!(3, len);
    ///
    /// assert_eq!("ƒoo".len(), 4); // fancy f!
    /// assert_eq!("ƒoo".chars().count(), 3);
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
    /// # use cursed_strings::str;
    /// let s: &str = "".into();
    /// assert!(s.is_empty());
    ///
    /// let s: &str = "not empty".into();
    /// assert!(!s.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Checks that `index`-th byte is the first byte in a UTF-8 code point
    /// sequence or the end of the string.
    ///
    /// The start and end of the string (when `index == self.len()`) are
    /// considered to be boundaries.
    ///
    /// Returns `false` if `index` is greater than `self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::str;
    /// let s: &str = "Löwe 老虎 Léopard".into();
    /// assert!(s.is_char_boundary(0));
    /// // start of `老`
    /// assert!(s.is_char_boundary(6));
    /// assert!(s.is_char_boundary(s.len()));
    ///
    /// // second byte of `ö`
    /// assert!(!s.is_char_boundary(2));
    ///
    /// // third byte of `老`
    /// assert!(!s.is_char_boundary(8));
    /// ```
    #[inline]
    pub fn is_char_boundary(&self, index: usize) -> bool {
        // 0 is always ok.
        // Test for 0 explicitly so that it can optimize out the check
        // easily and skip reading string data for that case.
        // Note that optimizing `self.get(..index)` relies on this.
        if index == 0 {
            return true;
        }

        match self.as_bytes().get(index) {
            // For `None` we have two options:
            //
            // - index == self.len()
            //   Empty strings are valid, so return true
            // - index > self.len()
            //   In this case return false
            //
            // The check is placed exactly here, because it improves generated
            // code on higher opt-levels. See PR #84751 for more details.
            None => index == self.len(),

            // This is bit magic equivalent to: b < 128 || b >= 192
            Some(&b) => (b as i8) >= -0x40,
        }
    }

    /// Converts a string slice to a byte slice. To convert the byte slice back
    /// into a string slice, use the [`from_utf8`] function.
    ///
    /// [`from_utf8`]: crate::from_utf8
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::str;
    /// let bytes = <&str>::from("bors").as_bytes();
    /// assert_eq!(b"bors", bytes);
    /// ```
    #[inline(always)]
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY: const sound because we transmute two types with the same layout
        unsafe { std::mem::transmute(self.storage.as_ref()) }
    }

    /// Converts a mutable string slice to a mutable byte slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the content of the slice is valid UTF-8
    /// before the borrow ends and the underlying `str` is used.
    ///
    /// Use of a `str` whose contents are not valid UTF-8 is undefined behavior.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::String;
    /// let mut s = String::from("Hello");
    /// let bytes = unsafe { s.as_bytes_mut() };
    ///
    /// assert_eq!(bytes, b"Hello");
    /// ```
    ///
    /// Mutability:
    ///
    /// ```
    /// # use cursed_strings::String;
    /// let mut s = String::from("🗻∈🌏");
    ///
    /// unsafe {
    ///     let bytes = s.as_bytes_mut();
    ///
    ///     bytes[0] = 0xF0;
    ///     bytes[1] = 0x9F;
    ///     bytes[2] = 0x8D;
    ///     bytes[3] = 0x94;
    /// }
    ///
    /// assert_eq!(s, "🍔∈🌏");
    /// ```
    #[inline(always)]
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8]
    where
        S: AsMut<[u8]>,
    {
        // SAFETY: const sound because we transmute two types with the same layout
        std::mem::transmute(self.storage.as_mut())
    }

    /// Converts a string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`u8`]. This pointer will be pointing to the first byte of the string
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
    /// # use cursed_strings::str;
    /// let s: &str = "Hello".into();
    /// let ptr = s.as_ptr();
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.storage.as_ref() as *const [u8] as *const u8
    }

    /// Converts a mutable string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`u8`]. This pointer will be pointing to the first byte of the string
    /// slice.
    ///
    /// It is your responsibility to make sure that the string slice only gets
    /// modified in a way that it remains valid UTF-8.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8
    where
        S: AsMut<[u8]>,
    {
        self.storage.as_mut() as *mut [u8] as *mut u8
    }

    /// Returns a subslice of `str`.
    ///
    /// This is the non-panicking alternative to indexing the `str`. Returns
    /// [`None`] whenever equivalent indexing operation would panic.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::{str, String};
    /// let v = String::from("🗻∈🌏");
    ///
    /// assert_eq!(v.get(0..4), Some(<&str>::from("🗻")));
    ///
    /// // indices not on UTF-8 sequence boundaries
    /// assert!(v.get(1..).is_none());
    /// assert!(v.get(..8).is_none());
    ///
    /// // out of bounds
    /// assert!(v.get(..42).is_none());
    /// ```
    #[inline]
    pub fn get<I: SliceIndex<StringBase<[u8]>>>(&self, i: I) -> Option<&I::Output> {
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
    /// # use cursed_strings::{str, String};
    /// let mut v = String::from("hello");
    /// // correct length
    /// assert!(v.get_mut(0..5).is_some());
    /// // out of bounds
    /// assert!(v.get_mut(..42).is_none());
    /// assert_eq!(v.get_mut(0..2).map(|v| &*v), Some(<&str>::from("he")));
    ///
    /// assert_eq!(v, "hello");
    /// {
    ///     let s = v.get_mut(0..2);
    ///     let s = s.map(|s| {
    ///         s.make_ascii_uppercase();
    ///         &*s
    ///     });
    ///     assert_eq!(s, Some(<&str>::from("HE")));
    /// }
    /// assert_eq!(v, "HEllo");
    /// ```
    #[inline]
    pub fn get_mut<I: SliceIndex<StringBase<[u8]>>>(&mut self, i: I) -> Option<&mut I::Output>
    where
        S: AsMut<[u8]>,
    {
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
    /// # use cursed_strings::String;
    /// let v = "🗻∈🌏";
    /// unsafe {
    ///     assert_eq!(v.get_unchecked(0..4), "🗻");
    ///     assert_eq!(v.get_unchecked(4..7), "∈");
    ///     assert_eq!(v.get_unchecked(7..11), "🌏");
    /// }
    /// ```
    #[inline]
    pub unsafe fn get_unchecked<I: SliceIndex<StringBase<[u8]>>>(&self, i: I) -> &I::Output {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked`;
        // the slice is dereferencable because `self` is a safe reference.
        // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
        &*i.get_unchecked(&*self.as_ref())
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
    /// # use cursed_strings::String;
    /// let mut v = String::from("🗻∈🌏");
    /// unsafe {
    ///     assert_eq!(v.get_unchecked_mut(0..4), "🗻");
    ///     assert_eq!(v.get_unchecked_mut(4..7), "∈");
    ///     assert_eq!(v.get_unchecked_mut(7..11), "🌏");
    /// }
    /// ```
    #[inline]
    pub unsafe fn get_unchecked_mut<I: SliceIndex<StringBase<[u8]>>>(
        &mut self,
        i: I,
    ) -> &mut I::Output
    where
        S: AsMut<[u8]>,
    {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked_mut`;
        // the slice is dereferencable because `self` is a safe reference.
        // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
        &mut *i.get_unchecked_mut(&mut *self.as_mut())
    }

    /// Divide one string slice into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a UTF-8 code point.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`split_at_mut`]
    /// method.
    ///
    /// [`split_at_mut`]: str::split_at_mut
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
    /// # use cursed_strings::str;
    /// let s: &str = "Per Martin-Löf".into();
    ///
    /// let (first, last) = s.split_at(3);
    ///
    /// assert_eq!(first, "Per");
    /// assert_eq!(last, " Martin-Löf");
    /// ```
    #[inline]
    pub fn split_at(&self, mid: usize) -> (&StringBase<[u8]>, &StringBase<[u8]>) {
        // is_char_boundary checks that the index is in [0, .len()]
        if self.is_char_boundary(mid) {
            // SAFETY: just checked that `mid` is on a char boundary.
            unsafe {
                (
                    self.get_unchecked(0..mid),
                    self.get_unchecked(mid..self.len()),
                )
            }
        } else {
            slice_error_fail(self.as_ref(), 0, mid)
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
    /// [`split_at`]: StringBase::split_at
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
    /// # use cursed_strings::String;
    /// let mut s = String::from("Per Martin-Löf");
    /// {
    ///     let (first, last) = s.split_at_mut(3);
    ///     first.make_ascii_uppercase();
    ///     assert_eq!(first, "PER");
    ///     assert_eq!(last, " Martin-Löf");
    /// }
    /// assert_eq!(s, "PER Martin-Löf");
    /// ```
    #[inline]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut StringBase<[u8]>, &mut StringBase<[u8]>)
    where
        S: AsMut<[u8]>,
    {
        // is_char_boundary checks that the index is in [0, .len()]
        if self.is_char_boundary(mid) {
            let len = self.len();
            let ptr = self.as_mut_ptr();
            // SAFETY: just checked that `mid` is on a char boundary.
            unsafe {
                (
                    from_utf8_unchecked_mut(core::slice::from_raw_parts_mut(ptr, mid)),
                    from_utf8_unchecked_mut(core::slice::from_raw_parts_mut(
                        ptr.add(mid),
                        len - mid,
                    )),
                )
            }
        } else {
            slice_error_fail(self.as_ref(), 0, mid)
        }
    }

    /// Returns an iterator over the [`char`]s of a string slice.
    ///
    /// As a string slice consists of valid UTF-8, we can iterate through a
    /// string slice by [`char`]. This method returns such an iterator.
    ///
    /// It's important to remember that [`char`] represents a Unicode Scalar
    /// Value, and may not match your idea of what a 'character' is. Iteration
    /// over grapheme clusters may be what you actually want. This functionality
    /// is not provided by Rust's standard library, check crates.io instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::str;
    /// let word = <&str>::from("goodbye");
    ///
    /// let count = word.chars().count();
    /// assert_eq!(7, count);
    ///
    /// let mut chars = word.chars();
    ///
    /// assert_eq!(Some('g'), chars.next());
    /// assert_eq!(Some('o'), chars.next());
    /// assert_eq!(Some('o'), chars.next());
    /// assert_eq!(Some('d'), chars.next());
    /// assert_eq!(Some('b'), chars.next());
    /// assert_eq!(Some('y'), chars.next());
    /// assert_eq!(Some('e'), chars.next());
    ///
    /// assert_eq!(None, chars.next());
    /// ```
    ///
    /// Remember, [`char`]s may not match your intuition about characters:
    ///
    /// [`char`]: prim@char
    ///
    /// ```
    /// let y = "y̆";
    ///
    /// let mut chars = y.chars();
    ///
    /// assert_eq!(Some('y'), chars.next()); // not 'y̆'
    /// assert_eq!(Some('\u{0306}'), chars.next());
    ///
    /// assert_eq!(None, chars.next());
    /// ```
    #[inline]
    pub fn chars(&self) -> Chars<'_> {
        let s: &str = self.into();
        s.chars()
    }
    pub fn char_indices(&self) -> CharIndices<'_> {
        let s: &str = self.into();
        s.char_indices()
    }

    /// An iterator over the bytes of a string slice.
    ///
    /// As a string slice consists of a sequence of bytes, we can iterate
    /// through a string slice by byte. This method returns such an iterator.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use cursed_strings::str;
    /// let mut bytes = <&str>::from("bors").bytes();
    ///
    /// assert_eq!(Some(b'b'), bytes.next());
    /// assert_eq!(Some(b'o'), bytes.next());
    /// assert_eq!(Some(b'r'), bytes.next());
    /// assert_eq!(Some(b's'), bytes.next());
    ///
    /// assert_eq!(None, bytes.next());
    /// ```
    #[inline]
    pub fn bytes(&self) -> Bytes<'_> {
        let s: &str = self.into();
        s.bytes()
    }

    /// Checks if all characters in this string are within the ASCII range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::str;
    /// let ascii = <&str>::from("hello!\n");
    /// let non_ascii = <&str>::from("Grüße, Jürgen ❤");
    ///
    /// assert!(ascii.is_ascii());
    /// assert!(!non_ascii.is_ascii());
    /// ```
    #[inline]
    pub fn is_ascii(&self) -> bool {
        // We can treat each byte as character here: all multibyte characters
        // start with a byte that is not in the ascii range, so we will stop
        // there already.
        self.as_bytes().is_ascii()
    }

    /// Checks that two strings are an ASCII case-insensitive match.
    ///
    /// Same as `to_ascii_lowercase(a) == to_ascii_lowercase(b)`,
    /// but without allocating and copying temporaries.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cursed_strings::str;
    /// assert!(<&str>::from("Ferris").eq_ignore_ascii_case("FERRIS".into()));
    /// assert!(<&str>::from("Ferrös").eq_ignore_ascii_case("FERRöS".into()));
    /// assert!(!<&str>::from("Ferrös").eq_ignore_ascii_case("FERRÖS".into()));
    /// ```
    #[inline]
    pub fn eq_ignore_ascii_case(&self, other: &StringBase<[u8]>) -> bool {
        self.as_bytes().eq_ignore_ascii_case(other.as_bytes())
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
    /// # use cursed_strings::String;
    /// let mut s = String::from("Grüße, Jürgen ❤");
    ///
    /// s.make_ascii_uppercase();
    ///
    /// assert_eq!(s, "GRüßE, JüRGEN ❤");
    /// ```
    #[inline]
    pub fn make_ascii_uppercase(&mut self)
    where
        S: AsMut<[u8]>,
    {
        // SAFETY: safe because we transmute two types with the same layout.
        let me = unsafe { self.as_bytes_mut() };
        me.make_ascii_uppercase()
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
    /// # use cursed_strings::String;
    /// let mut s = String::from("GRÜßE, JÜRGEN ❤");
    ///
    /// s.make_ascii_lowercase();
    ///
    /// assert_eq!(s, "grÜße, jÜrgen ❤");
    /// ```
    #[inline]
    pub fn make_ascii_lowercase(&mut self)
    where
        S: AsMut<[u8]>,
    {
        // SAFETY: safe because we transmute two types with the same layout.
        let me = unsafe { self.as_bytes_mut() };
        me.make_ascii_lowercase()
    }
}

#[inline(never)]
#[cold]
#[track_caller]
pub(crate) fn slice_error_fail(s: &StringBase<[u8]>, begin: usize, end: usize) -> ! {
    const MAX_DISPLAY_LENGTH: usize = 256;
    let (truncated, s_trunc) = truncate_to_char_boundary(s, MAX_DISPLAY_LENGTH);
    let ellipsis = if truncated { "[...]" } else { "" };

    // 1. out of bounds
    if begin > s.len() || end > s.len() {
        let oob_index = if begin > s.len() { begin } else { end };
        panic!(
            "byte index {} is out of bounds of `{}`{}",
            oob_index, s_trunc, ellipsis
        );
    }

    // 2. begin <= end
    assert!(
        begin <= end,
        "begin <= end ({} <= {}) when slicing `{}`{}",
        begin,
        end,
        s_trunc,
        ellipsis
    );

    // 3. character boundary
    let index = if !s.is_char_boundary(begin) {
        begin
    } else {
        end
    };
    // find the character
    let mut char_start = index;
    while !s.is_char_boundary(char_start) {
        char_start -= 1;
    }
    // `char_start` must be less than len and a char boundary
    let ch = s[char_start..].chars().next().unwrap();
    let char_range = char_start..char_start + ch.len_utf8();
    panic!(
        "byte index {} is not a char boundary; it is inside {:?} (bytes {:?}) of `{}`{}",
        index, ch, char_range, s_trunc, ellipsis
    );
}
