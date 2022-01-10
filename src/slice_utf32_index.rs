use core::slice::SliceIndex;

use crate::string_base::StringBase;

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
unsafe impl SliceIndex<StringBase<[char]>> for core::ops::RangeFull {
    type Output = StringBase<[char]>;
    #[inline]
    fn get(self, slice: &StringBase<[char]>) -> Option<&Self::Output> {
        Some(slice)
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[char]>) -> Option<&mut Self::Output> {
        Some(slice)
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[char]>) -> *const Self::Output {
        slice
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[char]>) -> *mut Self::Output {
        slice
    }
    #[inline]
    fn index(self, slice: &StringBase<[char]>) -> &Self::Output {
        slice
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[char]>) -> &mut Self::Output {
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
/// Panics if `begin > end`, or if `end > len`.
unsafe impl SliceIndex<StringBase<[char]>> for core::ops::Range<usize> {
    type Output = StringBase<[char]>;
    #[inline]
    fn get(self, slice: &StringBase<[char]>) -> Option<&Self::Output> {
        if self.start <= self.end && self.end <= slice.len() {
            Some(unsafe { &*self.get_unchecked(slice) })
        } else {
            None
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[char]>) -> Option<&mut Self::Output> {
        if self.start <= self.end && self.end <= slice.len() {
            // SAFETY: just checked that `start` and `end` are on a char boundary.
            // We know the pointer is unique because we got it from `slice`.
            Some(unsafe { &mut *self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[char]>) -> *const Self::Output {
        let slice = slice as *const [char];
        // SAFETY: the caller guarantees that `self` is in bounds of `slice`
        // which satisfies all the conditions for `add`.
        let ptr = slice.as_ptr().add(self.start);
        let len = self.end - self.start;
        core::ptr::slice_from_raw_parts(ptr, len) as *const StringBase<[char]>
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[char]>) -> *mut Self::Output {
        let slice = slice as *mut [char];
        // SAFETY: see comments for `get_unchecked`.
        let ptr = slice.as_mut_ptr().add(self.start);
        let len = self.end - self.start;
        core::ptr::slice_from_raw_parts_mut(ptr, len) as *mut StringBase<[char]>
    }
    #[inline]
    fn index(self, slice: &StringBase<[char]>) -> &Self::Output {
        let end = self.end;
        match self.get(slice) {
            Some(s) => s,

            #[cfg(feature = "alloc")]
            None => panic!("char index {} is out of bounds of `{}`", end, &*slice),

            #[cfg(not(feature = "alloc"))]
            None => panic!("char index {} is out of bounds", end),
        }
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[char]>) -> &mut Self::Output {
        if self.start <= self.end && self.end <= slice.len() {
            // SAFETY: just checked that `start` and `end` are on a char boundary.
            // We know the pointer is unique because we got it from `slice`.
            unsafe { &mut *self.get_unchecked_mut(slice) }
        } else {
            #[cfg(feature = "alloc")]
            panic!("char index {} is out of bounds of `{}`", self.end, &*slice);

            #[cfg(not(feature = "alloc"))]
            panic!("char index {} is out of bounds", self.end);
        }
    }
}

/// Implements substring slicing with syntax `&self[.. end]` or `&mut
/// self[.. end]`.
///
/// Returns a slice of the given string from the char range [`0`, `end`).
/// Equivalent to `&self[0 .. end]` or `&mut self[0 .. end]`.
///
/// This operation is *O*(1).
///
/// Prior to 1.20.0, these indexing operations were still supported by
/// direct implementation of `Index` and `IndexMut`.
///
/// # Panics
///
/// Panics if `end > len`.
unsafe impl SliceIndex<StringBase<[char]>> for core::ops::RangeTo<usize> {
    type Output = StringBase<[char]>;
    #[inline]
    fn get(self, slice: &StringBase<[char]>) -> Option<&Self::Output> {
        if self.end <= slice.len() {
            // SAFETY: just checked that `end` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &*self.get_unchecked(slice) })
        } else {
            None
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[char]>) -> Option<&mut Self::Output> {
        if self.end <= slice.len() {
            // SAFETY: just checked that `end` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &mut *self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[char]>) -> *const Self::Output {
        let slice = slice as *const [char];
        let ptr = slice.as_ptr();
        core::ptr::slice_from_raw_parts(ptr, self.end) as *const StringBase<[char]>
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[char]>) -> *mut Self::Output {
        let slice = slice as *mut [char];
        let ptr = slice.as_mut_ptr();
        core::ptr::slice_from_raw_parts_mut(ptr, self.end) as *mut StringBase<[char]>
    }
    #[inline]
    fn index(self, slice: &StringBase<[char]>) -> &Self::Output {
        let end = self.end;
        match self.get(slice) {
            Some(s) => s,

            #[cfg(feature = "alloc")]
            None => panic!("char index {} is out of bounds of `{}`", end, &*slice),

            #[cfg(not(feature = "alloc"))]
            None => panic!("char index {} is out of bounds", end),
        }
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[char]>) -> &mut Self::Output {
        if self.end <= slice.len() {
            // SAFETY: just checked that `end` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            unsafe { &mut *self.get_unchecked_mut(slice) }
        } else {
            #[cfg(feature = "alloc")]
            panic!("char index {} is out of bounds of `{}`", self.end, &*slice);

            #[cfg(not(feature = "alloc"))]
            panic!("char index {} is out of bounds", self.end);
        }
    }
}

/// Implements substring slicing with syntax `&self[begin ..]` or `&mut
/// self[begin ..]`.
///
/// Returns a slice of the given string from the char range [`begin`,
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
/// Panics if `begin > len`.
unsafe impl SliceIndex<StringBase<[char]>> for core::ops::RangeFrom<usize> {
    type Output = StringBase<[char]>;
    #[inline]
    fn get(self, slice: &StringBase<[char]>) -> Option<&Self::Output> {
        if self.start <= slice.len() {
            // SAFETY: just checked that `start` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &*self.get_unchecked(slice) })
        } else {
            None
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[char]>) -> Option<&mut Self::Output> {
        if self.start <= slice.len() {
            // SAFETY: just checked that `start` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            Some(unsafe { &mut *self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[char]>) -> *const Self::Output {
        let slice = slice as *const [char];
        // SAFETY: the caller guarantees that `self` is in bounds of `slice`
        // which satisfies all the conditions for `add`.
        let ptr = slice.as_ptr().add(self.start);
        let len = slice.len() - self.start;
        core::ptr::slice_from_raw_parts(ptr, len) as *const StringBase<[char]>
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[char]>) -> *mut Self::Output {
        let slice = slice as *mut [char];
        // SAFETY: identical to `get_unchecked`.
        let ptr = slice.as_mut_ptr().add(self.start);
        let len = slice.len() - self.start;
        core::ptr::slice_from_raw_parts_mut(ptr, len) as *mut StringBase<[char]>
    }
    #[inline]
    fn index(self, slice: &StringBase<[char]>) -> &Self::Output {
        let start = self.start;
        match self.get(slice) {
            Some(s) => s,

            #[cfg(feature = "alloc")]
            None => panic!("char index {} is out of bounds of `{}`", start, &*slice),

            #[cfg(not(feature = "alloc"))]
            None => panic!("char index {} is out of bounds", start),
        }
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[char]>) -> &mut Self::Output {
        if self.start <= slice.len() {
            // SAFETY: just checked that `start` is on a char boundary,
            // and we are passing in a safe reference, so the return value will also be one.
            unsafe { &mut *self.get_unchecked_mut(slice) }
        } else {
            #[cfg(feature = "alloc")]
            panic!(
                "char index {} is out of bounds of `{}`",
                self.start, &*slice
            );

            #[cfg(not(feature = "alloc"))]
            panic!("char index {} is out of bounds", self.start);
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
unsafe impl SliceIndex<StringBase<[char]>> for core::ops::RangeToInclusive<usize> {
    type Output = StringBase<[char]>;
    #[inline]
    fn get(self, slice: &StringBase<[char]>) -> Option<&Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get(slice)
        }
    }
    #[inline]
    fn get_mut(self, slice: &mut StringBase<[char]>) -> Option<&mut Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get_mut(slice)
        }
    }
    #[inline]
    unsafe fn get_unchecked(self, slice: *const StringBase<[char]>) -> *const Self::Output {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked`.
        (..self.end + 1).get_unchecked(slice)
    }
    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut StringBase<[char]>) -> *mut Self::Output {
        // SAFETY: the caller must uphold the safety contract for `get_unchecked_mut`.
        (..self.end + 1).get_unchecked_mut(slice)
    }
    #[inline]
    fn index(self, slice: &StringBase<[char]>) -> &Self::Output {
        if self.end == usize::MAX {
            str_index_overflow_fail();
        }
        (..self.end + 1).index(slice)
    }
    #[inline]
    fn index_mut(self, slice: &mut StringBase<[char]>) -> &mut Self::Output {
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
