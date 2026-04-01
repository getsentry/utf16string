//! The [`SliceIndex`] trait and implementations.
//!
//! This supports all slicing for [`WStr`] and [`WString`].

use core::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

use byteorder::ByteOrder;

use crate::WStr;
#[cfg(any(feature = "alloc", feature = "std"))]
use crate::WString;

mod private {
    use super::*;

    pub trait SealedSliceIndex {}

    impl SealedSliceIndex for RangeFull {}
    impl SealedSliceIndex for Range<usize> {}
    impl SealedSliceIndex for RangeFrom<usize> {}
    impl SealedSliceIndex for RangeTo<usize> {}
    impl SealedSliceIndex for RangeInclusive<usize> {}
    impl SealedSliceIndex for RangeToInclusive<usize> {}
}
/// Our own version of [`core::slice::SliceIndex`].
///
/// Since this is a sealed trait, we need to re-define this trait.  This trait itself is
/// sealed as well.
pub trait SliceIndex<T>: private::SealedSliceIndex
where
    T: ?Sized,
{
    /// The result of slicing, another slice of the same type as you started with normally.
    type Output: ?Sized;

    /// Returns a shared reference to the output at this location, if in bounds.
    fn get(self, slice: &T) -> Option<&Self::Output>;

    /// Returns a mutable reference to the output at this location, if in bounds.
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;

    /// Like [`SliceIndex::get`] but without bounds checking.
    ///
    /// # Safety
    ///
    /// You must guarantee the resulting slice is valid UTF-16LE, otherwise you will get
    /// undefined behaviour.
    unsafe fn get_unchecked(self, slice: &T) -> &Self::Output;

    /// Like [`SliceIndex::get_mut`] but without bounds checking.
    ///
    /// # Safety
    ///
    /// You must guarantee the resulting slice is valid UTF-16LE, otherwise you will get
    /// undefined behavour.
    unsafe fn get_unchecked_mut(self, slice: &mut T) -> &mut Self::Output;

    /// Returns a shared reference to the output at this location, panicking if out of bounds.
    fn index(self, slice: &T) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, panicking if out of bounds.
    fn index_mut(self, slice: &mut T) -> &mut Self::Output;
}

/// Implments substring slicing with syntax `&self[..]` or `&mut self[..]`.
///
/// Unlike other implementations this can never panic.
impl<E> SliceIndex<WStr<E>> for RangeFull
where
    E: ByteOrder,
{
    type Output = WStr<E>;

    #[inline]
    fn get(self, slice: &WStr<E>) -> Option<&Self::Output> {
        Some(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut WStr<E>) -> Option<&mut Self::Output> {
        Some(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &WStr<E>) -> &Self::Output {
        slice
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        slice
    }

    #[inline]
    fn index(self, slice: &WStr<E>) -> &Self::Output {
        slice
    }

    #[inline]
    fn index_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        slice
    }
}

/// Implements substring slicing with syntax `&self[begin .. end]` or `&mut self[begin .. end]`.
impl<E> SliceIndex<WStr<E>> for Range<usize>
where
    E: ByteOrder,
{
    type Output = WStr<E>;

    #[inline]
    fn get(self, slice: &WStr<E>) -> Option<&Self::Output> {
        if self.start <= self.end
            && slice.is_char_boundary(self.start)
            && slice.is_char_boundary(self.end)
        {
            Some(unsafe { self.get_unchecked(slice) })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut WStr<E>) -> Option<&mut Self::Output> {
        if self.start <= self.end
            && slice.is_char_boundary(self.start)
            && slice.is_char_boundary(self.end)
        {
            Some(unsafe { self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &WStr<E>) -> &Self::Output {
        let ptr = slice.as_ptr().add(self.start);
        let len = self.end - self.start;
        WStr::from_utf16_unchecked(core::slice::from_raw_parts(ptr, len))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        let ptr = slice.as_mut_ptr().add(self.start);
        let len = self.end - self.start;
        WStr::from_utf16_unchecked_mut(core::slice::from_raw_parts_mut(ptr, len))
    }

    #[inline]
    fn index(self, slice: &WStr<E>) -> &Self::Output {
        self.get(slice).expect("slice index out of bounds")
    }

    #[inline]
    fn index_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        self.get_mut(slice).expect("slice index out of bounds")
    }
}

/// Implements substring slicing with syntax `&self[.. end]` or `&mut self[.. end]`.
impl<E> SliceIndex<WStr<E>> for RangeTo<usize>
where
    E: ByteOrder,
{
    type Output = WStr<E>;

    #[inline]
    fn get(self, slice: &WStr<E>) -> Option<&Self::Output> {
        if slice.is_char_boundary(self.end) {
            Some(unsafe { self.get_unchecked(slice) })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut WStr<E>) -> Option<&mut Self::Output> {
        if slice.is_char_boundary(self.end) {
            Some(unsafe { self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &WStr<E>) -> &Self::Output {
        let ptr = slice.as_ptr();
        WStr::from_utf16_unchecked(core::slice::from_raw_parts(ptr, self.end))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        let ptr = slice.as_mut_ptr();
        WStr::from_utf16_unchecked_mut(core::slice::from_raw_parts_mut(ptr, self.end))
    }

    #[inline]
    fn index(self, slice: &WStr<E>) -> &Self::Output {
        self.get(slice).expect("slice index out of bounds")
    }

    #[inline]
    fn index_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        self.get_mut(slice).expect("slice index out of bounds")
    }
}

/// Implements substring slicing with syntax `&self[begin ..]` or `&mut self[begin ..]`.
impl<E> SliceIndex<WStr<E>> for RangeFrom<usize>
where
    E: ByteOrder,
{
    type Output = WStr<E>;

    #[inline]
    fn get(self, slice: &WStr<E>) -> Option<&Self::Output> {
        if slice.is_char_boundary(self.start) {
            Some(unsafe { self.get_unchecked(slice) })
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut WStr<E>) -> Option<&mut Self::Output> {
        if slice.is_char_boundary(self.start) {
            Some(unsafe { self.get_unchecked_mut(slice) })
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &WStr<E>) -> &Self::Output {
        let ptr = slice.as_ptr().add(self.start);
        let len = slice.len() - self.start;
        WStr::from_utf16_unchecked(core::slice::from_raw_parts(ptr, len))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        let ptr = slice.as_mut_ptr().add(self.start);
        let len = slice.len() - self.start;
        WStr::from_utf16_unchecked_mut(core::slice::from_raw_parts_mut(ptr, len))
    }

    #[inline]
    fn index(self, slice: &WStr<E>) -> &Self::Output {
        self.get(slice).expect("slice index out of bounds")
    }

    #[inline]
    fn index_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        self.get_mut(slice).expect("slice index out of bounds")
    }
}

/// Implements substring slicing with syntax `&self[begin ..= end]` or `&mut self[begin ..= end]`.
impl<E> SliceIndex<WStr<E>> for RangeInclusive<usize>
where
    E: ByteOrder,
{
    type Output = WStr<E>;

    #[inline]
    fn get(self, slice: &WStr<E>) -> Option<&Self::Output> {
        if *self.end() == usize::MAX {
            None
        } else {
            (*self.start()..self.end() + 1).get(slice)
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut WStr<E>) -> Option<&mut Self::Output> {
        if *self.end() == usize::MAX {
            None
        } else {
            (*self.start()..self.end() + 1).get_mut(slice)
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &WStr<E>) -> &Self::Output {
        (*self.start()..self.end() + 1).get_unchecked(slice)
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        (*self.start()..self.end() + 1).get_unchecked_mut(slice)
    }

    #[inline]
    fn index(self, slice: &WStr<E>) -> &Self::Output {
        if *self.end() == usize::MAX {
            panic!("index overflow");
        }
        (*self.start()..self.end() + 1).index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        if *self.end() == usize::MAX {
            panic!("index overflow");
        }
        (*self.start()..self.end() + 1).index_mut(slice)
    }
}

/// Implements substring slicing with syntax `&self[..= end]` or `&mut self[..= end]`.
impl<E> SliceIndex<WStr<E>> for RangeToInclusive<usize>
where
    E: ByteOrder,
{
    type Output = WStr<E>;

    #[inline]
    fn get(self, slice: &WStr<E>) -> Option<&Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get(slice)
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut WStr<E>) -> Option<&mut Self::Output> {
        if self.end == usize::MAX {
            None
        } else {
            (..self.end + 1).get_mut(slice)
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &WStr<E>) -> &Self::Output {
        (..self.end + 1).get_unchecked(slice)
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        (..self.end + 1).get_unchecked_mut(slice)
    }

    #[inline]
    fn index(self, slice: &WStr<E>) -> &Self::Output {
        if self.end == usize::MAX {
            panic!("index overflow");
        }
        (..self.end + 1).index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut WStr<E>) -> &mut Self::Output {
        if self.end == usize::MAX {
            panic!("index overflow");
        }
        (..self.end + 1).index_mut(slice)
    }
}

impl<I, E> Index<I> for WStr<E>
where
    I: SliceIndex<WStr<E>>,
    E: ByteOrder,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

impl<I, E> IndexMut<I> for WStr<E>
where
    I: SliceIndex<WStr<E>>,
    E: ByteOrder,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
impl<I, E> Index<I> for WString<E>
where
    I: SliceIndex<WStr<E>>,
    E: ByteOrder,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
impl<I, E> IndexMut<I> for WString<E>
where
    I: SliceIndex<WStr<E>>,
    E: ByteOrder,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

#[cfg(test)]
#[cfg(any(feature = "alloc", feature = "std"))]
mod tests {
    use super::*;

    #[test]
    fn test_wstr_range() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let t = &s[2..8];

        assert_eq!(t.to_utf8(), "ell");
    }

    #[test]
    fn test_wstr_range_to() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let t = &s[..8];

        assert_eq!(t.to_utf8(), "hell");
    }

    #[test]
    fn test_wstr_range_from() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let t = &s[2..];

        assert_eq!(t.to_utf8(), "ello");
    }

    #[test]
    fn test_wstr_range_full() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let t = &s[..];

        assert_eq!(t.to_utf8(), "hello");
    }

    #[test]
    fn test_wstr_range_inclusive() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let t = &s[2..=7];

        assert_eq!(t.to_utf8(), "ell");
    }

    #[test]
    fn test_wstr_range_to_inclusive() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let t = &s[..=7];

        assert_eq!(t.to_utf8(), "hell");
    }

    #[test]
    fn test_wstring_range() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WString::from_utf16le(b.to_vec()).unwrap();
        let t = &s[2..8];

        assert_eq!(t.to_utf8(), "ell");
    }

    #[test]
    fn test_wstring_range_to() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WString::from_utf16le(b.to_vec()).unwrap();
        let t = &s[..8];

        assert_eq!(t.to_utf8(), "hell");
    }

    #[test]
    fn test_wstring_range_from() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WString::from_utf16le(b.to_vec()).unwrap();
        let t = &s[2..];

        assert_eq!(t.to_utf8(), "ello");
    }

    #[test]
    fn test_wstring_range_full() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WString::from_utf16le(b.to_vec()).unwrap();
        let t = &s[..];

        assert_eq!(t.to_utf8(), "hello");
    }

    #[test]
    fn test_wstring_range_inclusive() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WString::from_utf16le(b.to_vec()).unwrap();
        let t = &s[2..=7];

        assert_eq!(t.to_utf8(), "ell");
    }

    #[test]
    fn test_wstring_range_to_inclusive() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WString::from_utf16le(b.to_vec()).unwrap();
        let t = &s[..=7];

        assert_eq!(t.to_utf8(), "hell");
    }
}
