use core::{
    slice::SliceIndex,
    str::{Bytes, CharIndices, Chars},
};

use crate::{from_utf8_unchecked_mut, validation::truncate_to_char_boundary, StringSlice};

#[allow(non_camel_case_types)]
/// Exactly the same as [`std::primitive::str`], except generic
pub type str = StringSlice<u8>;

impl str {
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
    /// # use generic_str::str;
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
    /// # use generic_str::str;
    /// let s: &str = "".into();
    /// assert!(s.is_empty());
    ///
    /// let s: &str = "not empty".into();
    /// assert!(!s.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
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
    /// # use generic_str::str;
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
    /// # use generic_str::str;
    /// let bytes = <&str>::from("bors").as_bytes();
    /// assert_eq!(b"bors", bytes);
    /// ```
    #[inline(always)]
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY: const sound because we transmute two types with the same layout
        unsafe { core::mem::transmute(self.storage.as_ref()) }
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
    /// # use generic_str::String;
    /// let mut s = String::from("Hello");
    /// let bytes = unsafe { s.as_bytes_mut() };
    ///
    /// assert_eq!(bytes, b"Hello");
    /// ```
    ///
    /// Mutability:
    ///
    /// ```
    /// # use generic_str::{str, String};
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
    /// assert_eq!(s, <&str>::from("🍔∈🌏"));
    /// ```
    #[inline(always)]
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        // SAFETY: const sound because we transmute two types with the same layout
        core::mem::transmute(self.storage.as_mut())
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
    /// # use generic_str::str;
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
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
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
    /// # use generic_str::{str, String};
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
    /// # use generic_str::{str, String};
    /// let mut v = String::from("hello");
    /// // correct length
    /// assert!(v.get_mut(0..5).is_some());
    /// // out of bounds
    /// assert!(v.get_mut(..42).is_none());
    /// assert_eq!(v.get_mut(0..2).map(|v| &*v), Some(<&str>::from("he")));
    ///
    /// assert_eq!(v, <&str>::from("hello"));
    /// {
    ///     let s = v.get_mut(0..2);
    ///     let s = s.map(|s| {
    ///         s.make_ascii_uppercase();
    ///         &*s
    ///     });
    ///     assert_eq!(s, Some(<&str>::from("HE")));
    /// }
    /// assert_eq!(v, <&str>::from("HEllo"));
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
    /// # use generic_str::str;
    /// let v = <&str>::from("🗻∈🌏");
    /// unsafe {
    ///     assert_eq!(v.get_unchecked(0..4), <&str>::from("🗻"));
    ///     assert_eq!(v.get_unchecked(4..7), <&str>::from("∈"));
    ///     assert_eq!(v.get_unchecked(7..11), <&str>::from("🌏"));
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
    /// # use generic_str::{str, String};
    /// let mut v = String::from("🗻∈🌏");
    /// unsafe {
    ///     assert_eq!(v.get_unchecked_mut(0..4), <&str>::from("🗻"));
    ///     assert_eq!(v.get_unchecked_mut(4..7), <&str>::from("∈"));
    ///     assert_eq!(v.get_unchecked_mut(7..11), <&str>::from("🌏"));
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
    /// # use generic_str::str;
    /// let s: &str = "Per Martin-Löf".into();
    ///
    /// let (first, last) = s.split_at(3);
    ///
    /// assert_eq!(first, <&str>::from("Per"));
    /// assert_eq!(last, <&str>::from(" Martin-Löf"));
    /// ```
    #[inline]
    pub fn split_at(&self, mid: usize) -> (&Self, &Self) {
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
            slice_error_fail(self, 0, mid)
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
    /// [`split_at`]: str::split_at
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
    /// # use generic_str::{str, String};
    /// let mut s = String::from("Per Martin-Löf");
    /// {
    ///     let (first, last) = s.split_at_mut(3);
    ///     first.make_ascii_uppercase();
    ///     assert_eq!(first, <&str>::from("PER"));
    ///     assert_eq!(last, <&str>::from(" Martin-Löf"));
    /// }
    /// assert_eq!(s, <&str>::from("PER Martin-Löf"));
    /// ```
    #[inline]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
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
            slice_error_fail(self, 0, mid)
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
    /// # use generic_str::str;
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
        let s: &core::primitive::str = self.into();
        s.chars()
    }
    pub fn char_indices(&self) -> CharIndices<'_> {
        let s: &core::primitive::str = self.into();
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
    /// # use generic_str::str;
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
        let s: &core::primitive::str = self.into();
        s.bytes()
    }

    /// Checks if all characters in this string are within the ASCII range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use generic_str::str;
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
    /// # use generic_str::str;
    /// assert!(<&str>::from("Ferris").eq_ignore_ascii_case("FERRIS".into()));
    /// assert!(<&str>::from("Ferrös").eq_ignore_ascii_case("FERRöS".into()));
    /// assert!(!<&str>::from("Ferrös").eq_ignore_ascii_case("FERRÖS".into()));
    /// ```
    #[inline]
    pub fn eq_ignore_ascii_case(&self, other: &Self) -> bool {
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
    /// # use generic_str::{str, String};
    /// let mut s = String::from("Grüße, Jürgen ❤");
    ///
    /// s.make_ascii_uppercase();
    ///
    /// assert_eq!(s, <&str>::from("GRüßE, JüRGEN ❤"));
    /// ```
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
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
    /// # use generic_str::{str, String};
    /// let mut s = String::from("GRÜßE, JÜRGEN ❤");
    ///
    /// s.make_ascii_lowercase();
    ///
    /// assert_eq!(s, <&str>::from("grÜße, jÜrgen ❤"));
    /// ```
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        // SAFETY: safe because we transmute two types with the same layout.
        let me = unsafe { self.as_bytes_mut() };
        me.make_ascii_lowercase()
    }

    /// Returns the lowercase equivalent of this string slice, as a new [`String`].
    ///
    /// 'Lowercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Lowercase`.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [`String`] instead of modifying the
    /// parameter in-place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::str;
    /// let s = <&str>::from("HELLO");
    ///
    /// assert_eq!(s.to_lowercase(), <&str>::from("hello"));
    /// ```
    ///
    /// A tricky example, with sigma:
    ///
    /// ```
    /// # use generic_str::str;
    /// let sigma = <&str>::from("Σ");
    ///
    /// assert_eq!(sigma.to_lowercase(), <&str>::from("σ"));
    ///
    /// // but at the end of a word, it's ς, not σ:
    /// let odysseus = <&str>::from("ὈΔΥΣΣΕΎΣ");
    ///
    /// assert_eq!(odysseus.to_lowercase(), <&str>::from("ὀδυσσεύς"));
    /// ```
    ///
    /// Languages without case are not changed:
    ///
    /// ```
    /// # use generic_str::str;
    /// let new_year = <&str>::from("农历新年");
    ///
    /// assert_eq!(new_year, new_year.to_lowercase());
    /// ```
    #[cfg(feature = "alloc")]
    pub fn to_lowercase(&self) -> crate::String {
        use core::unicode::conversions;

        let mut s = crate::String::with_capacity(self.len());
        for (i, c) in self[..].char_indices() {
            if c == 'Σ' {
                // Σ maps to σ, except at the end of a word where it maps to ς.
                // This is the only conditional (contextual) but language-independent mapping
                // in `SpecialCasing.txt`,
                // so hard-code it rather than have a generic "condition" mechanism.
                // See https://github.com/rust-lang/rust/issues/26035
                map_uppercase_sigma(self, i, &mut s)
            } else {
                match conversions::to_lower(c) {
                    [a, '\0', _] => s.push(a),
                    [a, b, '\0'] => {
                        s.push(a);
                        s.push(b);
                    }
                    [a, b, c] => {
                        s.push(a);
                        s.push(b);
                        s.push(c);
                    }
                }
            }
        }
        return s;

        fn map_uppercase_sigma(from: &str, i: usize, to: &mut crate::String) {
            // See http://www.unicode.org/versions/Unicode7.0.0/ch03.pdf#G33992
            // for the definition of `Final_Sigma`.
            debug_assert!('Σ'.len_utf8() == 2);
            let is_word_final = case_ignoreable_then_cased(from[..i].chars().rev())
                && !case_ignoreable_then_cased(from[i + 2..].chars());
            to.push_str(if is_word_final { "ς" } else { "σ" }.into());
        }

        fn case_ignoreable_then_cased<I: Iterator<Item = char>>(mut iter: I) -> bool {
            use core::unicode::{Case_Ignorable, Cased};
            match iter.find(|&c| !Case_Ignorable(c)) {
                Some(c) => Cased(c),
                None => false,
            }
        }
    }

    /// Returns the uppercase equivalent of this string slice, as a new [`String`].
    ///
    /// 'Uppercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Uppercase`.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [`String`] instead of modifying the
    /// parameter in-place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use generic_str::str;
    /// let s = <&str>::from("hello");
    ///
    /// assert_eq!(s.to_uppercase(), <&str>::from("HELLO"));
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// # use generic_str::str;
    /// let new_year = <&str>::from("农历新年");
    ///
    /// assert_eq!(new_year, new_year.to_uppercase());
    /// ```
    ///
    /// One character can become multiple:
    /// ```
    /// # use generic_str::str;
    /// let s = <&str>::from("tschüß");
    ///
    /// assert_eq!(s.to_uppercase(), <&str>::from("TSCHÜSS"));
    /// ```
    #[cfg(feature = "alloc")]
    pub fn to_uppercase(&self) -> crate::String {
        use core::unicode::conversions;

        let mut s = crate::String::with_capacity(self.len());
        for c in self[..].chars() {
            match conversions::to_upper(c) {
                [a, '\0', _] => s.push(a),
                [a, b, '\0'] => {
                    s.push(a);
                    s.push(b);
                }
                [a, b, c] => {
                    s.push(a);
                    s.push(b);
                    s.push(c);
                }
            }
        }
        s
    }
}

#[inline(never)]
#[cold]
#[track_caller]
pub(crate) fn slice_error_fail(s: &str, begin: usize, end: usize) -> ! {
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
