use std::marker::PhantomData;

use byteorder::ByteOrder;

use crate::{validate_raw_utf16, Utf16Error, WString};

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
    pub fn with_capcity(capacity: usize) -> Self {
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
}

#[cfg(test)]
mod tests {
    use byteorder::LE;

    use super::*;

    #[test]
    fn test_new() {
        let _s: WString<LE> = WString::new();
    }

    #[test]
    fn test_with_capacity() {
        let _s: WString<LE> = WString::with_capcity(5);
    }

    #[test]
    fn test_from_utf16() {
        let v = Vec::from(&b"h\x00e\x00l\x00l\x00o\x00"[..]);
        let s: WString<LE> = WString::from_utf16(v.clone()).unwrap();
        assert_eq!(s.buf, v);
    }
}
