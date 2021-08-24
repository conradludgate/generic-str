use core::str::next_code_point;
use std::iter::FusedIterator;

use crate::{validation::{next_code_point_reverse, utf8_is_cont_byte}};

#[derive(Clone)]
pub struct Chars<'a> {
    pub(super) iter: core::slice::Iter<'a, u8>,
}


impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        next_code_point(&mut self.iter).map(|ch| {
            // SAFETY: `str` invariant says `ch` is a valid Unicode Scalar Value.
            unsafe { char::from_u32_unchecked(ch) }
        })
    }

    #[inline]
    fn count(self) -> usize {
        // length in `char` is equal to the number of non-continuation bytes
        self.iter.filter(|&&byte| !utf8_is_cont_byte(byte)).count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.iter.len();
        // `(len + 3)` can't overflow, because we know that the `slice::Iter`
        // belongs to a slice in memory which has a maximum length of
        // `isize::MAX` (that's well below `usize::MAX`).
        ((len + 3) / 4, Some(len))
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        // No need to go through the entire string.
        self.next_back()
    }
}

impl std::fmt::Debug for Chars<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Chars(")?;
        f.debug_list().entries(self.clone()).finish()?;
        write!(f, ")")?;
        Ok(())
    }
}

impl<'a> DoubleEndedIterator for Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        next_code_point_reverse(&mut self.iter).map(|ch| {
            // SAFETY: `str` invariant says `ch` is a valid Unicode Scalar Value.
            unsafe { char::from_u32_unchecked(ch) }
        })
    }
}

impl FusedIterator for Chars<'_> {}


/// An iterator over the [`char`]s of a string slice, and their positions.
///
/// This struct is created by the [`char_indices`] method on [`str`].
/// See its documentation for more.
///
/// [`char`]: prim@char
/// [`char_indices`]: str::char_indices
#[derive(Clone, Debug)]
pub struct CharIndices<'a> {
    pub(super) front_offset: usize,
    pub(super) iter: Chars<'a>,
}

impl<'a> Iterator for CharIndices<'a> {
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<(usize, char)> {
        let pre_len = self.iter.iter.len();
        match self.iter.next() {
            None => None,
            Some(ch) => {
                let index = self.front_offset;
                let len = self.iter.iter.len();
                self.front_offset += pre_len - len;
                Some((index, ch))
            }
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<(usize, char)> {
        // No need to go through the entire string.
        self.next_back()
    }
}

impl<'a> DoubleEndedIterator for CharIndices<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<(usize, char)> {
        self.iter.next_back().map(|ch| {
            let index = self.front_offset + self.iter.iter.len();
            (index, ch)
        })
    }
}

impl FusedIterator for CharIndices<'_> {}
