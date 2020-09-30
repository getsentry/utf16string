//! Implementations for the [WString] type.
//!
//! The type itself lives in the lib.rs file to avoid having to have a public alias, but
//! implementations live here.

use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use byteorder::{BigEndian, ByteOrder, LittleEndian};

use crate::utf16::validate_raw_utf16;
use crate::{Utf16Error, WStr, WString};

impl WString<LittleEndian> {
    /// Creates a new [WString] from raw bytes in little-endian byte order.
    pub fn from_utf16le(buf: Vec<u8>) -> Result<Self, Utf16Error> {
        Self::from_utf16(buf)
    }

    /// Converts a vector of bytes to a [WString], not checking validity.
    ///
    /// # Safety
    ///
    /// You must ensure the vector contains already valid UTF-16 with little-endian
    /// byte-order, otherwise you will get undefined behaviour.
    #[inline]
    pub unsafe fn from_utf16le_unchecked(buf: Vec<u8>) -> Self {
        Self::from_utf16_unchecked(buf)
    }
}

impl WString<BigEndian> {
    /// Creates a new [WString] from raw bytes in big-endian byte-order.
    pub fn from_utf16be(buf: Vec<u8>) -> Result<Self, Utf16Error> {
        Self::from_utf16(buf)
    }

    /// Converts a vector of bytes to a [WString], not checking validity.
    ///
    /// # Safety
    ///
    /// You must ensure the vector contains already valid UTF-16 with big-endian byte-order,
    /// otherwise you will get undefined behaviour.
    #[inline]
    pub unsafe fn from_utf16be_unchecked(buf: Vec<u8>) -> Self {
        Self::from_utf16_unchecked(buf)
    }
}

impl<E> WString<E>
where
    E: ByteOrder,
{
    /// Creates a new empty [WString].
    #[inline]
    pub fn new() -> Self {
        Self {
            buf: Vec::new(),
            _endian: PhantomData,
        }
    }

    /// Creates a new empty [WString] with a capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buf: Vec::with_capacity(capacity),
            _endian: PhantomData,
        }
    }

    /// Converts a vector of bytes to a [WString].
    #[inline]
    pub fn from_utf16(buf: Vec<u8>) -> Result<Self, Utf16Error> {
        validate_raw_utf16::<E>(buf.as_slice())?;
        Ok(Self {
            buf,
            _endian: PhantomData,
        })
    }

    /// Converts a vector of bytes to a [WString], not checking validity.
    ///
    /// # Safety
    ///
    /// You must ensure the vector contains already valid UTF-16 in the correct byte-order,
    /// otherwise you will get undefined behaviour.
    #[inline]
    pub unsafe fn from_utf16_unchecked(buf: Vec<u8>) -> Self {
        Self {
            buf,
            _endian: PhantomData,
        }
    }

    /// Converts this string into a byte vector.
    #[inline]
    pub fn into_bytes(self) -> Vec<u8> {
        self.buf
    }

    /// Returns a `&WStr` slice containing the entire string.
    #[inline]
    pub fn as_wstr(&self) -> &WStr<E> {
        self
    }

    /// Returns a `&mut WStr` slice containing the entire string.
    #[inline]
    pub fn as_mut_wstr(&mut self) -> &mut WStr<E> {
        self
    }

    /// Appends a string slicie onto the end of this string.
    #[inline]
    pub fn push_wstr(&mut self, string: &WStr<E>) {
        self.buf.extend_from_slice(string.as_bytes())
    }

    /// Returns the capacity in bytes.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Ensure that this string has spare capacity of at least `additional` bytes.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.buf.reserve(additional)
    }

    /// Returns the length in bytes, not chars or graphemes.
    #[inline]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns `true` if the string has a [Self::len] of zero, `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<E> Default for WString<E>
where
    E: ByteOrder,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<E> Deref for WString<E>
where
    E: ByteOrder,
{
    type Target = WStr<E>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { WStr::from_utf16_unchecked(self.buf.as_slice()) }
    }
}

impl<E> DerefMut for WString<E>
where
    E: ByteOrder,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { WStr::from_utf16_unchecked_mut(self.buf.as_mut_slice()) }
    }
}

#[cfg(test)]
mod tests {
    use byteorder::LE;

    use super::*;

    #[test]
    fn test_new() {
        let s: WString<LE> = WString::new();
        assert_eq!(s.len(), 0);
        assert_eq!(s.capacity(), 0);
        assert_eq!(s.to_utf8(), "");
    }

    #[test]
    fn test_with_capacity() {
        let s: WString<LE> = WString::with_capacity(5);
        assert_eq!(s.capacity(), 5);
        assert_eq!(s.len(), 0);
        assert_eq!(s.to_utf8(), "");
    }

    #[test]
    fn test_from_utf16() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s: WString<LE> = WString::from_utf16(b.to_vec()).unwrap();
        assert_eq!(s.buf, b);
        assert_eq!(s.to_utf8(), "hello");
    }

    #[test]
    fn test_from_utf16_le_be() {
        let b_le = b"h\x00e\x00l\x00l\x00o\x00";
        let s_le = WString::from_utf16le(b_le.to_vec()).unwrap();
        assert_eq!(s_le.to_utf8(), "hello");

        let b_be = b"\x00h\x00e\x00l\x00l\x00o";
        let s_be = WString::from_utf16be(b_be.to_vec()).unwrap();
        assert_eq!(s_be.to_utf8(), "hello");
    }

    #[test]
    fn test_from_utf16_unchecked() {
        let b_le = b"h\x00e\x00l\x00l\x00o\x00";
        let s_le: WString<LE> = unsafe { WString::from_utf16_unchecked(b_le.to_vec()) };
        assert_eq!(s_le.to_utf8(), "hello");

        let s_le = unsafe { WString::from_utf16le_unchecked(b_le.to_vec()) };
        assert_eq!(s_le.to_utf8(), "hello");

        let b_be = b"\x00h\x00e\x00l\x00l\x00o";
        let s_be = unsafe { WString::from_utf16be_unchecked(b_be.to_vec()) };
        assert_eq!(s_be.to_utf8(), "hello");
    }

    #[test]
    fn test_into_bytes() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WString::from_utf16le(b.to_vec()).unwrap();
        assert_eq!(s.into_bytes(), b);
    }

    #[test]
    fn test_as_wstr() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let wstr = WStr::from_utf16le(b).unwrap();
        let wstring = WString::from_utf16le(b.to_vec()).unwrap();
        assert_eq!(wstr, wstring.as_wstr());
    }

    #[test]
    fn test_as_mut_wstr() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let wstr = WStr::from_utf16le(b).unwrap();
        let mut wstring = WString::from_utf16le(b.to_vec()).unwrap();
        let m: &mut WStr<_> = wstring.as_mut_wstr();
        assert_eq!(m, wstr);
    }

    #[test]
    fn test_push_wstr() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let mut wstring = WString::from_utf16le(b.to_vec()).unwrap();
        let b = b" \x00w\x00o\x00r\x00l\x00d\x00";
        let wstr = WStr::from_utf16le(b).unwrap();
        wstring.push_wstr(wstr);
        assert_eq!(wstring.to_utf8(), "hello world");
    }

    #[test]
    fn test_reserve() {
        let mut s: WString<LE> = WString::with_capacity(0);
        assert_eq!(s.capacity(), 0);
        s.reserve(42);
        assert!(s.capacity() >= 42);
    }

    #[test]
    fn test_deref() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let wstring = WString::from_utf16le(b.to_vec()).unwrap();
        let wstr = WStr::from_utf16le(b).unwrap();
        assert_eq!(wstring.deref(), wstr);
    }

    #[test]
    fn test_deref_mut() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let v = Vec::from(&b[..]);
        let mut s = WString::from_utf16le(v).unwrap();
        let wstr = s.deref_mut();
        unsafe {
            let buf = wstr.as_bytes_mut();
            buf.copy_from_slice(b"w\x00o\x00r\x00l\x00d\x00");
        }
        assert_eq!(s.to_utf8(), "world");
    }
}
