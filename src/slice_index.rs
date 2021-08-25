use std::slice::SliceIndex;

use crate::string_base::{StringBase, slice_error_fail};

/// Implements substring slicing with syntax `&self[..]` or `&mut self[..]`.
///
/// Returns a slice of the whole string, i.e., returns `&self` or `&mut
/// self`. Equivalent to `&self[0 .. len]` or `&mut self[0 .. len]`. Unlike
/// other indexing operations, this can never panic.
///
/// This operation is *O*(1).
///
/// Prior to 1.20.0, these indexing operations were still supported by
/// direct implementation of `Index` and `IndexMut`.
///
/// Equivalent to `&self[0 .. len]` or `&mut self[0 .. len]`.
unsafe impl SliceIndex<StringBase<[u8]>> for std::ops::RangeFull {
    type Output = StringBase<[u8]>;
    #[inline]
    fn get(self, slice: &StringBase<[u8]>) -> Option<&Self::Output> {
        Some(slice)
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[u8]>) -> Option<&mut Self::Output> {
        Some(slice)
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[u8]>) -> *const Self::Output {
        slice
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[u8]>) -> *mut Self::Output {
        slice
    }
    #[inline]
    fn index(self, slice: &StringBase<[u8]>) -> &Self::Output {
        slice
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[u8]>) -> &mut Self::Output {
        slice
    }
}

/// Implements substring slicing with syntax `&self[begin .. end]` or `&mut
/// self[begin .. end]`.
///
/// Returns a slice of the given string from the byte range
/// [`begin`, `end`).
///
/// This operation is *O*(1).
///
/// Prior to 1.20.0, these indexing operations were still supported by
/// direct implementation of `Index` and `IndexMut`.
///
/// # Panics
///
/// Panics if `begin` or `end` does not point to the starting byte offset of
/// a character (as defined by `is_char_boundary`), if `begin > end`, or if
/// `end > len`.
///
/// # Examples
///
/// ```
/// let s = "Löwe 老虎 Léopard";
/// assert_eq!(&s[0 .. 1], "L");
///
/// assert_eq!(&s[1 .. 9], "öwe 老");
///
/// // these will panic:
/// // byte 2 lies within `ö`:
/// // &s[2 ..3];
///
/// // byte 8 lies within `老`
/// // &s[1 .. 8];
///
/// // byte 100 is outside the string
/// // &s[3 .. 100];
/// ```
unsafe impl SliceIndex<StringBase<[u8]>> for std::ops::Range<usize> {
    type Output = StringBase<[u8]>;
    #[inline]
    fn get(self, slice: &StringBase<[u8]>) -> Option<&Self::Output> {
        if self.start <= self.end
            && slice.is_char_boundary(self.start)
            && slice.is_char_boundary(self.end)
        {
            // SAFETY: just checked that `start` and `end` are on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            // We also checked char boundaries, so this is valid UTF-8.
            Some(unsafe { &*self.get_unchecked(slice) })
        } else {
            None
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[u8]>) -> Option<&mut Self::Output> {
        if self.start <= self.end
            && slice.is_char_boundary(self.start)
            && slice.is_char_boundary(self.end)
        {
            // SAFETY: just checked that `start` and `end` are on a char boundary.
            // We know the pointer is unique because we got it from `slice`.
            Some(unsafe { &mut *self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[u8]>) -> *const Self::Output {
        let slice = slice as *const [u8];
        // SAFETY: the caller guarantees that `self` is in bounds of `slice`
        // which satisfies all the conditions for `add`.
        let ptr = slice.as_ptr().add(self.start);
        let len = self.end - self.start;
        std::ptr::slice_from_raw_parts(ptr, len) as *const StringBase<[u8]>
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[u8]>) -> *mut Self::Output {
        let slice = slice as *mut [u8];
        // SAFETY: see comments for `get_unchecked`.
        let ptr = slice.as_mut_ptr().add(self.start);
        let len = self.end - self.start;
        std::ptr::slice_from_raw_parts_mut(ptr, len) as *mut StringBase<[u8]>
    }
    #[inline]
    fn index(self, slice: &StringBase<[u8]>) -> &Self::Output {
        let (start, end) = (self.start, self.end);
        match self.get(slice) {
            Some(s) => s,
            None => slice_error_fail(slice, start, end),
        }
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[u8]>) -> &mut Self::Output {
        // is_char_boundary checks that the index is in [0, .len()]
        // cannot reuse `get` as above, because of NLL trouble
        if self.start <= self.end
            && slice.is_char_boundary(self.start)
            && slice.is_char_boundary(self.end)
        {
            // SAFETY: just checked that `start` and `end` are on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            unsafe { &mut *self.get_unchecked_mut(slice) }
        } else {
            slice_error_fail(slice, self.start, self.end)
        }
    }
}

/// Implements substring slicing with syntax `&self[.. end]` or `&mut
/// self[.. end]`.
///
/// Returns a slice of the given string from the byte range [`0`, `end`).
/// Equivalent to `&self[0 .. end]` or `&mut self[0 .. end]`.
///
/// This operation is *O*(1).
///
/// Prior to 1.20.0, these indexing operations were still supported by
/// direct implementation of `Index` and `IndexMut`.
///
/// # Panics
///
/// Panics if `end` does not point to the starting byte offset of a
/// character (as defined by `is_char_boundary`), or if `end > len`.
unsafe impl SliceIndex<StringBase<[u8]>> for std::ops::RangeTo<usize> {
    type Output = StringBase<[u8]>;
    #[inline]
    fn get(self, slice: &StringBase<[u8]>) -> Option<&Self::Output> {
        if slice.is_char_boundary(self.end) {
            // SAFETY: just checked that `end` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &*self.get_unchecked(slice) })
        } else {
            None
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[u8]>) -> Option<&mut Self::Output> {
        if slice.is_char_boundary(self.end) {
            // SAFETY: just checked that `end` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &mut *self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[u8]>) -> *const Self::Output {
        let slice = slice as *const [u8];
        let ptr = slice.as_ptr();
        std::ptr::slice_from_raw_parts(ptr, self.end) as *const StringBase<[u8]>
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[u8]>) -> *mut Self::Output {
        let slice = slice as *mut [u8];
        let ptr = slice.as_mut_ptr();
        std::ptr::slice_from_raw_parts_mut(ptr, self.end) as *mut StringBase<[u8]>
    }
    #[inline]
    fn index(self, slice: &StringBase<[u8]>) -> &Self::Output {
        let end = self.end;
        match self.get(slice) {
            Some(s) => s,
            None => slice_error_fail(slice, 0, end),
        }
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[u8]>) -> &mut Self::Output {
        if slice.is_char_boundary(self.end) {
            // SAFETY: just checked that `end` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            unsafe { &mut *self.get_unchecked_mut(slice) }
        } else {
            slice_error_fail(slice, 0, self.end)
        }
    }
}

/// Implements substring slicing with syntax `&self[begin ..]` or `&mut
/// self[begin ..]`.
///
/// Returns a slice of the given string from the byte range [`begin`,
/// `len`). Equivalent to `&self[begin .. len]` or `&mut self[begin ..
/// len]`.
///
/// This operation is *O*(1).
///
/// Prior to 1.20.0, these indexing operations were still supported by
/// direct implementation of `Index` and `IndexMut`.
///
/// # Panics
///
/// Panics if `begin` does not point to the starting byte offset of
/// a character (as defined by `is_char_boundary`), or if `begin > len`.
unsafe impl SliceIndex<StringBase<[u8]>> for std::ops::RangeFrom<usize> {
    type Output = StringBase<[u8]>;
    #[inline]
    fn get(self, slice: &StringBase<[u8]>) -> Option<&Self::Output> {
        if slice.is_char_boundary(self.start) {
            // SAFETY: just checked that `start` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &*self.get_unchecked(slice) })
        } else {
            None
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[u8]>) -> Option<&mut Self::Output> {
        if slice.is_char_boundary(self.start) {
            // SAFETY: just checked that `start` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &mut *self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[u8]>) -> *const Self::Output {
        let slice = slice as *const [u8];
        // SAFETY: the caller guarantees that `self` is in bounds of `slice`
        // which satisfies all the conditions for `add`.
        let ptr = slice.as_ptr().add(self.start);
        let len = slice.len() - self.start;
        std::ptr::slice_from_raw_parts(ptr, len) as *const StringBase<[u8]>
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[u8]>) -> *mut Self::Output {
        let slice = slice as *mut [u8];
        // SAFETY: identical to `get_unchecked`.
        let ptr = slice.as_mut_ptr().add(self.start);
        let len = slice.len() - self.start;
        std::ptr::slice_from_raw_parts_mut(ptr, len) as *mut StringBase<[u8]>
    }
    #[inline]
    fn index(self, slice: &StringBase<[u8]>) -> &Self::Output {
        let (start, end) = (self.start, slice.len());
        match self.get(slice) {
            Some(s) => s,
            None => slice_error_fail(slice, start, end),
        }
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[u8]>) -> &mut Self::Output {
        if slice.is_char_boundary(self.start) {
            // SAFETY: just checked that `start` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            unsafe { &mut *self.get_unchecked_mut(slice) }
        } else {
            slice_error_fail(slice, self.start, slice.len())
        }
    }
}

/// Implements substring slicing with syntax `&self[..= end]` or `&mut
/// self[..= end]`.
///
/// Returns a slice of the given string from the byte range [0, `end`].
/// Equivalent to `&self [0 .. end + 1]`, except if `end` has the maximum
/// value for `usize`.
///
/// This operation is *O*(1).
///
/// # Panics
///
/// Panics if `end` does not point to the ending byte offset of a character
/// (`end + 1` is either a starting byte offset as defined by
/// `is_char_boundary`, or equal to `len`), or if `end >= len`.
unsafe impl SliceIndex<StringBase<[u8]>> for std::ops::RangeToInclusive<usize> {
    type Output = StringBase<[u8]>;
    #[inline]
    fn get(self, slice: &StringBase<[u8]>) -> Option<&Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get(slice)
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[u8]>) -> Option<&mut Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get_mut(slice)
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[u8]>) -> *const Self::Output {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked`.
        (..self.end + 1).get_unchecked(slice)
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[u8]>) -> *mut Self::Output {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked_mut`.
        (..self.end + 1).get_unchecked_mut(slice)
    }
    #[inline]
    fn index(self, slice: &StringBase<[u8]>) -> &Self::Output {
        if self.end == usize::MAX {
            str_index_overflow_fail();
        }
        (..self.end + 1).index(slice)
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[u8]>) -> &mut Self::Output {
        if self.end == usize::MAX {
            str_index_overflow_fail();
        }
        (..self.end + 1).index_mut(slice)
    }
}

#[inline(never)]
#[cold]
#[track_caller]
fn str_index_overflow_fail() -> ! {
    panic!("attempted to index str up to maximum usize");
}
