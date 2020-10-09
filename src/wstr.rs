//! Implementations for the [`WStr`] type.
//!
//! The type itself lives in the `lib.rs` file to avoid having to have a public alias, but
//! implementations live here.

use std::fmt;

use byteorder::{BigEndian, ByteOrder, LittleEndian};

use crate::slicing::SliceIndex;
use crate::utf16::{is_trailing_surrogate, validate_raw_utf16};
use crate::{Utf16Error, WStr, WStrCharIndices, WStrChars};

impl WStr<LittleEndian> {
    /// Creates a new `&WStr<LE>`.
    pub fn from_utf16le(raw: &[u8]) -> Result<&Self, Utf16Error> {
        Self::from_utf16(raw)
    }

    /// Creates a new `&mut WStr<LE>`.
    pub fn from_utf16le_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        Self::from_utf16_mut(raw)
    }

    /// Creates a new [WStr] with little-endian byte-ordering.
    ///
    /// This is a shortcut to easily create `WStr<LE>` without having to specify the type
    /// explicitly.
    ///
    /// # Example
    ///
    /// ```
    /// use wstring::{LE, WStr};
    ///
    /// let b = b"h\x00i\x00";
    /// let s: &WStr<LE> = unsafe { WStr::from_utf16_unchecked(b) };
    /// let t = unsafe { WStr::from_utf16le_unchecked(b) };
    /// assert_eq!(s, t);
    /// ```
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// little-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16le_unchecked(raw: &[u8]) -> &Self {
        Self::from_utf16_unchecked(raw)
    }

    /// Creates a new `&mut WStr<LE>`.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// little-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16le_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        Self::from_utf16_unchecked_mut(raw)
    }
}

impl WStr<BigEndian> {
    /// Creates a new `&WStr<BE>`.
    pub fn from_utf16be(raw: &[u8]) -> Result<&Self, Utf16Error> {
        Self::from_utf16(raw)
    }

    /// Creates a new `&mut WStr<BE>`.
    pub fn from_utf16be_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        Self::from_utf16_mut(raw)
    }

    /// Creates a new `&WStr<BE>` from an existing byte-slice with big-endian byte-ordering.
    ///
    /// This is a shortcut to easily create `WStr<BE>` without having to specify the type
    /// explicitly.
    ///
    /// # Example
    ///
    /// ```
    /// use wstring::{BE, WStr};
    ///
    /// let b = b"h\x00i\x00";
    /// let s: &WStr<BE> = unsafe { WStr::from_utf16_unchecked(b) };
    /// let t = unsafe { WStr::from_utf16be_unchecked(b) };
    /// assert_eq!(s, t);
    /// ```
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// big-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16be_unchecked(raw: &[u8]) -> &Self {
        Self::from_utf16_unchecked(raw)
    }

    /// Creates a new `&mut WStr<BE>`.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// big-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16be_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        Self::from_utf16_unchecked_mut(raw)
    }
}

impl<E> WStr<E>
where
    E: ByteOrder,
{
    /// Creates a new `&WStr<E>` from an existing UTF-16 byte-slice.
    ///
    /// If the byte-slice is not valid [`Utf16Error`] is returned.
    pub fn from_utf16(raw: &[u8]) -> Result<&Self, Utf16Error> {
        validate_raw_utf16::<E>(raw)?;
        Ok(unsafe { Self::from_utf16_unchecked(raw) })
    }

    /// Creates a new `&mut WStr<E>` from an existing UTF-16 byte-slice.
    ///
    /// If the byte-slice is not valid [`Utf16Error`] is returned.
    pub fn from_utf16_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        validate_raw_utf16::<E>(raw)?;
        Ok(unsafe { Self::from_utf16_unchecked_mut(raw) })
    }

    /// Creates a new `&WStr<E>` from an existing UTF-16 byte-slice.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly otherwise you will
    /// get undefined behaviour.  Be aware of the byte-level endianess.
    pub unsafe fn from_utf16_unchecked(raw: &[u8]) -> &Self {
        &*(raw as *const [u8] as *const Self)
    }

    /// Like [`WStr::from_utf16_unchecked`] but return a mutable reference.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly otherwise you will
    /// get undefined behaviour.
    pub unsafe fn from_utf16_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        &mut *(raw as *mut [u8] as *mut Self)
    }

    /// The length in bytes, not chars or graphemes.
    #[inline]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns `true` if the [WStr::len] is zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the index into the bytes is on a char boundary.
    #[inline]
    pub fn is_char_boundary(&self, index: usize) -> bool {
        if index == 0 || index == self.len() {
            return true;
        }
        if index % 2 != 0 || index > self.len() {
            return false;
        }

        // Since we always have a valid UTF-16 string in here we now are sure we always
        // have a byte at index + 1.  The only invalid thing now is a trailing surrogate.
        let code_unit = E::read_u16(&self.raw[index..]);
        !is_trailing_surrogate(code_unit)
    }

    /// Converts to a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.raw
    }

    /// Converts to a mutable byte slice.
    ///
    /// # Safety
    ///
    /// When mutating the bytes it must still be valid encoded UTF-16 with the correct
    /// byte-order, otherwise you will get undefined behaviour.
    #[inline]
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.raw
    }

    /// Converts to a raw pointer to the byte slice.
    ///
    /// This is currently not `const fn` because this is not yet stable with a trait bound.
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.raw.as_ptr()
    }

    /// Converts to a mutable raw pointer to the byte slice.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.raw.as_mut_ptr()
    }

    /// Returns a subslice of `self`.
    ///
    /// The slice indices are on byte offsets of the underlying UTF-16 encoded buffer, if
    /// the subslice is not on character boundaries or otherwise invalid this will return
    /// [`None`].
    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&<I as SliceIndex<WStr<E>>>::Output>
    where
        I: SliceIndex<WStr<E>>,
    {
        index.get(self)
    }

    /// Returns a mutable subslice of `self`.
    ///
    /// The slice indices are on byte offsets of the underlying UTF-16 encoded buffer, if
    /// the subslice is not on character boundaries or otherwise invalid this will return
    /// [`None`].
    #[inline]
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut <I as SliceIndex<WStr<E>>>::Output>
    where
        I: SliceIndex<WStr<E>>,
    {
        index.get_mut(self)
    }

    /// Returns a subslice of `self`.
    ///
    /// # Safety
    ///
    /// Like [`WStr::get`] but this results in undefined behaviour if the sublice is not on
    /// character boundaries or otherwise invalid.
    #[inline]
    pub unsafe fn get_unchecked<I>(&self, index: I) -> &<I as SliceIndex<WStr<E>>>::Output
    where
        I: SliceIndex<WStr<E>>,
    {
        index.get_unchecked(self)
    }

    /// Returns a mutable subslice of `self`.
    ///
    /// # Safety
    ///
    /// Lice [`WStr::get_mut`] but this results in undefined behaviour if the subslice is
    /// not on character boundaries or otherwise invalid.
    #[inline]
    pub unsafe fn get_unchecked_mut<I>(
        &mut self,
        index: I,
    ) -> &mut <I as SliceIndex<WStr<E>>>::Output
    where
        I: SliceIndex<WStr<E>>,
    {
        index.get_unchecked_mut(self)
    }

    /// Returns an iterator of the [`char`]s of a string slice.
    #[inline]
    pub fn chars(&self) -> WStrChars<E> {
        WStrChars {
            chunks: self.raw.chunks_exact(2),
            _endian: self._endian,
        }
    }

    /// Returns and iterator over the [`char`]s of a string slice and their positions.
    #[inline]
    pub fn char_indices(&self) -> WStrCharIndices<E> {
        WStrCharIndices {
            chars: self.chars(),
            index: 0,
        }
    }

    /// Returns this [`WStr`] as a new owned [`String`].
    pub fn to_utf8(&self) -> String {
        self.chars().collect()
    }

    /// Returns `true` if all characters in the string are ASCII.
    #[inline]
    pub fn is_ascii(&self) -> bool {
        self.as_bytes().is_ascii()
    }
}

impl<E> AsRef<[u8]> for WStr<E>
where
    E: ByteOrder,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<E> fmt::Display for WStr<E>
where
    E: ByteOrder,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_utf8())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wstr_from_utf16le() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        assert_eq!(s.to_utf8(), "hello");

        // Odd number of bytes
        let b = b"h\x00e\x00l\x00l\x00o";
        let s = WStr::from_utf16le(b);
        assert!(s.is_err());

        // Lone leading surrogate
        let b = b"\x00\xd8x\x00";
        let s = WStr::from_utf16le(b);
        assert!(s.is_err());

        // Lone trailing surrogate
        let b = b"\x00\xdcx\x00";
        let s = WStr::from_utf16le(b);
        assert!(s.is_err());
    }

    #[test]
    fn test_wstr_from_utf16le_unchecked() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = unsafe { WStr::from_utf16le_unchecked(b) };
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_wstr_len() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        assert_eq!(s.len(), b.len());
    }

    #[test]
    fn test_wstr_is_empty() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        assert!(!s.is_empty());

        let s = WStr::from_utf16le(b"").unwrap();
        assert!(s.is_empty());
    }

    #[test]
    fn test_wstr_is_char_boundary() {
        let b = b"\x00\xd8\x00\xdcx\x00"; // "\u{10000}\u{78}"
        let s = WStr::from_utf16le(b).unwrap();
        assert!(s.is_char_boundary(0));
        assert!(!s.is_char_boundary(1));
        assert!(!s.is_char_boundary(2));
        assert!(!s.is_char_boundary(3));
        assert!(s.is_char_boundary(4));
        assert!(!s.is_char_boundary(5));
        assert!(s.is_char_boundary(6));
        assert!(!s.is_char_boundary(7)); // out of range
    }

    #[test]
    fn test_wstr_as_bytes() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        assert_eq!(s.as_bytes(), b);
    }

    #[test]
    fn test_wstr_as_bytes_mut() {
        let mut b = Vec::from(&b"h\x00e\x00l\x00l\x00o\x00"[..]);
        let s = WStr::from_utf16le_mut(b.as_mut_slice()).unwrap();
        let world = b"w\x00o\x00r\x00l\x00d\x00";
        unsafe {
            let buf = s.as_bytes_mut();
            buf.copy_from_slice(world);
        }
        assert_eq!(b.as_slice(), world);
    }

    #[test]
    fn test_wstr_get() {
        // This is implemented with get_unchecked() so this is also already tested.
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();

        let t = s.get(0..8).expect("expected Some(&WStr)");
        assert_eq!(t.as_bytes(), b"h\x00e\x00l\x00l\x00");

        let t = s.get(1..8);
        assert!(t.is_none());
    }

    #[test]
    fn test_wstr_get_mut() {
        // This is implemented with get_unchecked_mut() so this is also already tested.
        let mut b = Vec::from(&b"h\x00e\x00l\x00l\x00o\x00"[..]);
        let s = WStr::from_utf16le_mut(b.as_mut_slice()).unwrap();

        let t = s.get_mut(0..2).expect("expected Some(&mut Wstr)");
        unsafe {
            let buf = t.as_bytes_mut();
            buf.copy_from_slice(b"x\x00");
        }

        assert_eq!(s.as_bytes(), b"x\x00e\x00l\x00l\x00o\x00");
    }

    #[test]
    fn test_wstr_slice() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let sub = &s[2..8];
        assert_eq!(sub.as_bytes(), b"e\x00l\x00l\x00");
    }

    #[test]
    #[should_panic]
    fn test_wstr_bad_index() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let _r = &s[2..7];
    }

    #[test]
    fn test_wstr_to_utf8() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let out: String = s.to_utf8();
        assert_eq!(out, "hello");
    }

    #[test]
    fn test_wstr_is_ascii() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        assert!(s.is_ascii());

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        assert!(!s.is_ascii());
    }

    #[test]
    fn test_wstr_as_ref() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let r: &[u8] = s.as_ref();
        assert_eq!(r, b);
    }

    #[test]
    fn test_display() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        assert_eq!(format!("{}", s), "hello");
    }
}
