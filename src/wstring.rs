use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use byteorder::{BigEndian, ByteOrder, LittleEndian};

use crate::{validate_raw_utf16, Utf16Error, WStr, WString};

impl WString<LittleEndian> {
    /// Creates a new [WString] from raw bytes in little-endian byte order.
    pub fn from_utf16le(vec: Vec<u8>) -> Result<Self, Utf16Error> {
        Self::from_utf16(vec)
    }
}

impl WString<BigEndian> {
    /// Creates a new [WString] from raw bytes in big-endian byte-order.
    pub fn from_utf16be(vec: Vec<u8>) -> Result<Self, Utf16Error> {
        Self::from_utf16(vec)
    }
}

impl<E> WString<E>
where
    E: ByteOrder,
{
    /// Creates a new empty [WString].
    pub fn new() -> Self {
        Self {
            buf: Vec::new(),
            _endian: PhantomData,
        }
    }

    /// Creates a new empty [WString] with a capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buf: Vec::with_capacity(capacity),
            _endian: PhantomData,
        }
    }

    /// Converts a vector of bytes to a [WString].
    pub fn from_utf16(vec: Vec<u8>) -> Result<Self, Utf16Error> {
        validate_raw_utf16::<E>(vec.as_slice())?;
        Ok(Self {
            buf: vec,
            _endian: PhantomData,
        })
    }

    /// Returns the length in bytes, not chars or graphemes.
    #[inline]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns `true` if the string has a [len] of zero, `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the capacity in bytes.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
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
        unsafe { WStr::from_utf16_unchecked(&self.buf) }
    }
}

impl<E> DerefMut for WString<E>
where
    E: ByteOrder,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { WStr::from_utf16_unchecked_mut(&mut *self.buf) }
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
