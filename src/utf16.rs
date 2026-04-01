//! UTF-16 helper utilities.

use byteorder::ByteOrder;

use crate::Utf16Error;

/// Whether a code unit is a leading or high surrogate.
///
/// If a Unicode code point does not fit in one code unit (i.e. in one `u16`) it is split
/// into two code units called a *surrogate pair*.  The first code unit of this pair is the
/// *leading surrogate* and since it carries the high bits of the complete Unicode code
/// point it is also known as the *high surrogate*.
///
/// These surrogate code units have the first 6 bits set to a fixed prefix identifying
/// whether they are the *leading* or *trailing* code unit of the surrogate pair.  And for
/// the leading surrogate this bit prefix is `110110`, thus all leading surrogates have a
/// code unit between 0xD800-0xDBFF.
#[inline]
pub(crate) fn is_leading_surrogate(code_unit: u16) -> bool {
    code_unit & 0xFC00 == 0xD800
}

/// Whether a code unit is a trailing or low surrogate.
///
/// If a Unicode code point does not fit in one code unit (i.e. in one `u16`) it is split
/// into two code units called a *surrogate pair*.  The second code unit of this pair is the
/// *trailing surrogate* and since it carries the low bits of the complete Unicode code
/// point it is also know as the *low surrogate*.
///
/// These surrogate code unites have the first 6 bits set to a fixed prefix identifying
/// whether tye are the *leading* or *trailing* code unit of the surrogate pair.  Anf for
/// the trailing surrogate this bit prefix is `110111`, thus all trailing surrogates have a
/// code unit between 0xDC00-0xDFFF.
#[inline]
pub(crate) fn is_trailing_surrogate(code_unit: u16) -> bool {
    code_unit & 0xFC00 == 0xDC00
}

/// Decodes a surrogate pair of code units into a char.
///
/// This results in undefined behaviour if the code units do not form a valid surrogate
/// pair.
#[inline]
pub(crate) unsafe fn decode_surrogates(u: u16, u2: u16) -> char {
    #![allow(unused_unsafe)]
    debug_assert!(
        is_leading_surrogate(u),
        "first code unit not a leading surrogate"
    );
    debug_assert!(
        is_trailing_surrogate(u2),
        "second code unit not a trailing surrogate"
    );
    let c = (((u - 0xD800) as u32) << 10 | (u2 - 0xDC00) as u32) + 0x1_0000;
    // SAFETY: This is now guaranteed a valid Unicode code point.
    unsafe { core::char::from_u32_unchecked(c) }
}

/// Checks that the raw bytes are valid UTF-16LE.
///
/// When an error occurs this code needs to set `error_len` to skip forward 2 bytes,
/// *unless* we have a lone leading surrogate and are at the end of the input slice in which
/// case we need to return `None.
///
/// We compute `valid_up_to` lazily for performance, even though it's a little more verbose.
pub(crate) fn validate_raw_utf16<E: ByteOrder>(raw: &[u8]) -> Result<(), Utf16Error> {
    let base_ptr = raw.as_ptr() as usize;
    let mut chunks = raw.chunks_exact(core::mem::size_of::<u16>());

    while let Some(chunk) = chunks.next() {
        let code_point_ptr = chunk.as_ptr() as usize;
        let code_point = E::read_u16(chunk);

        if is_trailing_surrogate(code_point) {
            return Err(Utf16Error {
                valid_up_to: code_point_ptr - base_ptr,
                error_len: Some(core::mem::size_of::<u16>() as u8),
            });
        }

        if is_leading_surrogate(code_point) {
            match chunks.next().map(E::read_u16) {
                Some(u2) => {
                    if !is_trailing_surrogate(u2) {
                        return Err(Utf16Error {
                            valid_up_to: code_point_ptr - base_ptr,
                            error_len: Some(core::mem::size_of::<u16>() as u8),
                        });
                    }
                }
                None => {
                    return Err(Utf16Error {
                        valid_up_to: code_point_ptr - base_ptr,
                        error_len: None,
                    });
                }
            }
        }
    }

    let remainder = chunks.remainder();
    if !remainder.is_empty() {
        return Err(Utf16Error {
            valid_up_to: remainder.as_ptr() as usize - base_ptr,
            error_len: None,
        });
    }

    Ok(())
}

/// Extension trait for UTF-16 utilities on [`char`].
pub(crate) trait Utf16CharExt {
    /// Returns the number of bytes this character encodes into.
    ///
    /// The [`char::len_utf16`] method from the standard library returns the size in number
    /// of u16 code units instead of in bytes.  This provides a character length method
    /// which matches a string's length (`len`) definition.
    fn encoded_utf16_len(self) -> usize;

    /// Encodes this char, writing it into a bytes buffer.
    ///
    /// Returns the number of bytes written.
    ///
    /// Panics if the destination buffer is too small.
    fn encode_utf16_into<E: ByteOrder>(self, buf: &mut [u8]) -> usize;
}

impl Utf16CharExt for char {
    #[inline]
    fn encoded_utf16_len(self) -> usize {
        let code_point: u32 = self.into();
        if code_point & 0xFFFF == code_point {
            2
        } else {
            4
        }
    }

    #[inline]
    fn encode_utf16_into<E: ByteOrder>(self, mut buf: &mut [u8]) -> usize {
        let mut code_point: u32 = self.into();

        if (code_point & 0xFFFF) == code_point {
            assert!(buf.len() >= 2, "destination too small, need 2 bytes");
            E::write_u16(&mut buf, code_point as u16);
            2
        } else {
            assert!(buf.len() >= 4, "destination too small, need 4 bytes");
            code_point -= 0x1_0000;
            let code_unit0: u16 = 0xD800 | ((code_point >> 10) as u16);
            let code_unit1: u16 = 0xDC00 | ((code_point as u16) & 0x3FF);
            E::write_u16(&mut buf, code_unit0);
            E::write_u16(&mut buf[2..], code_unit1);
            4
        }
    }
}

#[cfg(test)]
#[cfg(any(feature = "alloc", feature = "std"))]
mod tests {
    use super::*;

    use crate::{WStr, LE};

    #[cfg(feature = "alloc")]
    use alloc::vec;

    #[test]
    fn test_is_leading_surrogate() {
        assert!(is_leading_surrogate(0xd800));

        // Regression test: bit pattern of 0xf800 starts with 0b111110, which has all bits
        // of 0b110110 set but is outside of the surrogate range.
        assert!(!is_leading_surrogate(0xf800));
    }

    #[test]
    fn test_is_trailing_surrogate() {
        assert!(is_trailing_surrogate(0xDC00));

        // regression test: bit pattern of 0xfc00 starts with 0b11111, which has all
        // bits of 0b110111 set but is outside of the surrogate range.
        assert!(!is_trailing_surrogate(0xfc00));
    }

    #[test]
    fn test_wstr_utf16error() {
        // This actually tests validate_raw_utf16(), but via the public APIs.

        // Lone trailing surrogate in 2nd char
        let b = b"h\x00\x00\xdce\x00l\x00l\x00o\x00";
        let e = WStr::from_utf16le(b).err().unwrap();
        assert_eq!(e.valid_up_to(), 2);
        assert_eq!(e.error_len(), Some(2));

        let head = WStr::from_utf16le(&b[..e.valid_up_to()]).unwrap();
        assert_eq!(head.to_utf8(), "h");

        let start = e.valid_up_to() + e.error_len().unwrap();
        let tail = WStr::from_utf16le(&b[start..]).unwrap();
        assert_eq!(tail.to_utf8(), "ello");

        // Leading surrogate, missing trailing surrogate in 2nd char
        let b = b"h\x00\x00\xd8e\x00l\x00l\x00o\x00";
        let e = WStr::from_utf16le(b).err().unwrap();
        assert_eq!(e.valid_up_to(), 2);
        assert_eq!(e.error_len(), Some(2));

        let head = WStr::from_utf16le(&b[..e.valid_up_to()]).unwrap();
        assert_eq!(head.to_utf8(), "h");

        let start = e.valid_up_to() + e.error_len().unwrap();
        let tail = WStr::from_utf16le(&b[start..]).unwrap();
        assert_eq!(tail.to_utf8(), "ello");

        // End of input
        let b = b"h\x00e\x00l\x00l\x00o\x00\x00\xd8";
        let e = WStr::from_utf16le(b).err().unwrap();
        assert_eq!(e.valid_up_to(), 10);
        assert_eq!(e.error_len(), None);

        // End of input, single byte
        let b = b"h\x00e\x00l\x00l\x00o\x00 ";
        let e = WStr::from_utf16le(b).err().unwrap();
        assert_eq!(e.valid_up_to(), 10);
        assert_eq!(e.error_len(), None);
    }

    #[test]
    fn test_utf16_char_ext_encode_utf16_into() {
        let mut v = vec![0u8; 10];
        let slice = v.as_mut_slice();
        let ret = 'a'.encode_utf16_into::<LE>(slice);
        assert_eq!(ret, 2);
        assert_eq!(&slice[..2], b"a\x00");

        let ret = '\u{10000}'.encode_utf16_into::<LE>(&mut slice[2..]);
        assert_eq!(ret, 4);
        assert_eq!(&v.as_slice()[..6], b"a\x00\x00\xd8\x00\xdc");
    }

    #[test]
    #[should_panic]
    fn test_utf16_char_ext_encode_utf16_into_too_small_single_unit() {
        let mut v = vec![0u8; 1];
        'a'.encode_utf16_into::<LE>(v.as_mut_slice());
    }

    #[test]
    #[should_panic]
    fn test_utf16_char_ext_encode_utf16_into_too_small_surrogate() {
        let mut v = vec![0u8; 3];
        '\u{10000}'.encode_utf16_into::<LE>(v.as_mut_slice());
    }

    #[test]
    fn test_utf16_char_ext_len_utf16_bytes() {
        let l0 = 'c'.encoded_utf16_len();
        let l1 = 'c'.len_utf16() * core::mem::size_of::<u16>();
        assert_eq!(l0, l1);
        assert_eq!(l0, 2);

        let l0 = '\u{10000}'.encoded_utf16_len();
        let l1 = '\u{10000}'.len_utf16() * core::mem::size_of::<u16>();
        assert_eq!(l0, l1);
        assert_eq!(l0, 4);
    }
}
