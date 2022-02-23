//! Implementation for the various char iterators.
//!
//! The type itself lives in the lib.rs file to avoid having to have a public alias, but
//! implementations live here.

use byteorder::ByteOrder;

use core::iter::FusedIterator;

use crate::utf16::{decode_surrogates, is_leading_surrogate, is_trailing_surrogate, Utf16CharExt};
use crate::{WStrCharIndices, WStrChars};

impl<'a, E> Iterator for WStrChars<'a, E>
where
    E: ByteOrder,
{
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Our input is valid UTF-16, so we can take a lot of shortcuts.
        let chunk = self.chunks.next()?;
        let u = E::read_u16(chunk);

        if !is_leading_surrogate(u) {
            // SAFETY: This is now guaranteed a valid Unicode code point.
            Some(unsafe { core::char::from_u32_unchecked(u as u32) })
        } else {
            let chunk = self.chunks.next().expect("missing trailing surrogate");
            let u2 = E::read_u16(chunk);
            debug_assert!(
                is_trailing_surrogate(u2),
                "code unit not a trailing surrogate"
            );
            Some(unsafe { decode_surrogates(u, u2) })
        }
    }

    #[inline]
    fn count(self) -> usize {
        // No need to fully construct all characters
        self.chunks
            .filter(|bb| !is_trailing_surrogate(E::read_u16(bb)))
            .count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, E> FusedIterator for WStrChars<'a, E> where E: ByteOrder {}

impl<'a, E> DoubleEndedIterator for WStrChars<'a, E>
where
    E: ByteOrder,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // Our input is valid UTF-16, so we can take a lot of shortcuts.
        let chunk = self.chunks.next_back()?;
        let u = E::read_u16(chunk);

        if !is_trailing_surrogate(u) {
            // SAFETY: This is now guaranteed a valid Unicode code point.
            Some(unsafe { core::char::from_u32_unchecked(u as u32) })
        } else {
            let chunk = self.chunks.next_back().expect("missing leading surrogate");
            let u2 = E::read_u16(chunk);
            debug_assert!(
                is_leading_surrogate(u2),
                "code unit not a leading surrogate"
            );
            Some(unsafe { decode_surrogates(u2, u) })
        }
    }
}

impl<'a, E> Iterator for WStrCharIndices<'a, E>
where
    E: ByteOrder,
{
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.index;
        let c = self.chars.next()?;
        self.index += c.encoded_utf16_len();
        Some((pos, c))
    }

    #[inline]
    fn count(self) -> usize {
        // No need to fully construct all characters
        self.chars.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, E> DoubleEndedIterator for WStrCharIndices<'a, E>
where
    E: ByteOrder,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let c = self.chars.next_back()?;
        let pos = self.index + self.chars.chunks.len() * core::mem::size_of::<u16>();
        Some((pos, c))
    }
}

impl<'a, E> FusedIterator for WStrCharIndices<'a, E> where E: ByteOrder {}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use crate::WStr;

    #[test]
    fn test_wstr_chars() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['\u{10000}', 'x']);

        // Regression: this leading surrogate used to be badly detected.
        let b = b"\x41\xf8A\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['\u{f841}', 'A']);
    }

    #[test]
    fn test_wstr_chars_reverse() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().rev().collect();
        assert_eq!(chars, vec!['o', 'l', 'l', 'e', 'h']);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().rev().collect();
        assert_eq!(chars, vec!['x', '\u{10000}']);
    }

    #[test]
    fn test_wstr_chars_last() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let c = s.chars().last().unwrap();
        assert_eq!(c, 'o');

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let c = s.chars().last().unwrap();
        assert_eq!(c, 'x');
    }

    #[test]
    fn test_wstr_chars_count() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let n = s.chars().count();
        assert_eq!(n, 5);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let n = s.chars().count();
        assert_eq!(n, 2);
    }

    #[test]
    fn test_wstr_char_indices() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().collect();
        assert_eq!(
            chars,
            vec![(0, 'h'), (2, 'e'), (4, 'l'), (6, 'l'), (8, 'o')]
        );

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().collect();
        assert_eq!(chars, vec![(0, '\u{10000}'), (4, 'x')]);
    }

    #[test]
    fn test_wstr_char_indices_reverse() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().rev().collect();
        assert_eq!(
            chars,
            vec![(8, 'o'), (6, 'l'), (4, 'l'), (2, 'e'), (0, 'h')]
        );

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<(usize, char)> = s.char_indices().rev().collect();
        assert_eq!(chars, vec![(4, 'x'), (0, '\u{10000}')]);
    }

    #[test]
    fn test_wstr_char_indices_last() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (8, 'o'));

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let c = s.char_indices().last().unwrap();
        assert_eq!(c, (4, 'x'));
    }

    #[test]
    fn test_wstr_char_indices_count() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let n = s.char_indices().count();
        assert_eq!(n, 5);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let n = s.char_indices().count();
        assert_eq!(n, 2);
    }
}
