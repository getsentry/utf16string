//! A UTF-16 little-endian string type.
//!
//! The main type in this crate is [WStr] which is a type similar to [str] but with the
//! underlying data encoded as UTF-16 with little-endian byte order.
//!
//! # Examples
//!
//! ```
//! use wstring::{WStr, LittleEndian};
//!
//! let b = b"h\x00e\x00l\x00l\x00o\x00";
//! let s: &WStr<LittleEndian> = WStr::from_utf16(b).unwrap();
//!
//! let chars: Vec<char> = s.chars().collect();
//! assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
//!
//! assert_eq!(s.to_utf8(), "hello");
//! ```

#![deny(missing_docs, missing_debug_implementations)]

use std::error::Error;
use std::fmt;
use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::slice::ChunksExact;

use byteorder::ByteOrder;

pub use byteorder::{BigEndian, LittleEndian, BE, LE};

mod slicing;
mod wstring;

#[doc(inline)]
pub use crate::slicing::SliceIndex;

/// Error for invalid UTF-16 encoded bytes.
#[derive(Debug, Copy, Clone)]
pub struct Utf16Error {}

impl fmt::Display for Utf16Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Invalid UTF-16LE data in byte slice")
    }
}

impl Error for Utf16Error {}

impl Utf16Error {
    /// Create a new [Utf16Error].
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for Utf16Error {
    fn default() -> Self {
        Self::new()
    }
}

/// A UTF-16 [String]-like type with little- or big-endian byte order.
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct WString<E: 'static + ByteOrder> {
    buf: Vec<u8>,
    _endian: PhantomData<&'static E>,
}

/// A UTF-16 [str]-like type with little- or big-endian byte order.
///
/// This mostly behaves like [str] does for UTF-8 encoded bytes slices, but works with
/// UTF-16 encoded byte slices.  The endianess is determined by the type parameter.
///
/// See the [module-level documentation](index.html) for some simple examples.
#[derive(Debug, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct WStr<E: 'static + ByteOrder> {
    _endian: PhantomData<&'static E>,
    raw: [u8],
}

impl WStr<LittleEndian> {
    /// Creates a new `&WStr<LE>`.
    pub fn from_utf16le(raw: &[u8]) -> Result<&Self, Utf16Error> {
        WStr::from_utf16(raw)
    }

    /// Creates a new `&mut WStr<LE>`.
    pub fn from_utf16le_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        WStr::from_utf16_mut(raw)
    }

    /// Creates a new [WStr] with little-endian byte-ordering.
    ///
    /// This is a shortcut to easily create `WStr<LE>` without having to specify the type
    /// explicitly.
    ///
    /// # Example
    ///
    /// ```
    /// use wstring::{WStr, LE};
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
        WStr::from_utf16_unchecked(raw)
    }

    /// Creates a new `&mut WStr<LE>`.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// little-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16le_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        WStr::from_utf16_unchecked_mut(raw)
    }
}

impl WStr<BigEndian> {
    /// Creates a new `&WStr<BE>`.
    pub fn from_utf16be(raw: &[u8]) -> Result<&Self, Utf16Error> {
        WStr::from_utf16(raw)
    }

    /// Creates a new `&mut WStr<BE>`.
    pub fn from_utf16be_mut(raw: &mut [u8]) -> Result<&mut Self, Utf16Error> {
        WStr::from_utf16_mut(raw)
    }

    /// Creates a new `&WStr<BE>` from an existing byte-slice with big-endian byte-ordering.
    ///
    /// This is a shortcut to easily create `WStr<BE>` without having to specify the type
    /// explicitly.
    ///
    /// # Example
    ///
    /// ```
    /// use wstring::{WStr, BE};
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
        WStr::from_utf16_unchecked(raw)
    }

    /// Creates a new `&mut WStr<BE>`.
    ///
    /// # Safety
    ///
    /// You must guarantee that the buffer passed in is encoded correctly as UTF-16 with
    /// big-endian byte-order, otherwise you will get undefined behaviour.
    pub unsafe fn from_utf16be_unchecked_mut(raw: &mut [u8]) -> &mut Self {
        WStr::from_utf16_unchecked_mut(raw)
    }
}

impl<E> WStr<E>
where
    E: ByteOrder,
{
    /// Creates a new `&WStr<E>` from an existing UTF-16 byte-slice.
    ///
    /// If the byte-slice is not valid [Utf16Error] is returned.
    pub fn from_utf16(raw: &[u8]) -> Result<&Self, Utf16Error> {
        validate_raw_utf16::<E>(raw)?;
        Ok(unsafe { Self::from_utf16_unchecked(raw) })
    }

    /// Creates a new `&mut WStr<E>` from an existing UTF-16 byte-slice.
    ///
    /// If the byte-slice is not valid [Utf16Error] is returned.
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

    /// Like [Self::from_utf16_unchecked] but return a mutable reference.
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

    /// Returns `true` if the [Self::len] is zero.
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
    /// `None`.
    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&<I as SliceIndex<WStr<E>>>::Output>
    where
        I: SliceIndex<WStr<E>>,
    {
        index.get(self)
    }

    /// Returns a mutable subslice of `Self`.
    ///
    /// The slice indices are on byte offsets of the underlying UTF-16 encoded buffer, if
    /// the subslice is not on character boundaries or otherwise invalid this will return
    /// `None`.
    #[inline]
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut <I as SliceIndex<WStr<E>>>::Output>
    where
        I: SliceIndex<WStr<E>>,
    {
        index.get_mut(self)
    }

    /// Returns a subslice of `Self`.
    ///
    /// # Safety
    ///
    /// Like [Self::get] but this results in undefined behaviour if the sublice is not on
    /// character boundaries or otherwise invalid.
    #[inline]
    pub unsafe fn get_unchecked<I>(&self, index: I) -> &<I as SliceIndex<WStr<E>>>::Output
    where
        I: SliceIndex<WStr<E>>,
    {
        index.get_unchecked(self)
    }

    /// Returns a mutable subslice of `Self`.
    ///
    /// # Safety
    ///
    /// Lice [Self::get_mut] but this results in undefined behaviour if the subslice is not
    /// on character boundaries or otherwise invalid.
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

    /// Returns an iterator of the [char]s of a string slice.
    #[inline]
    pub fn chars(&self) -> WStrChars<E> {
        WStrChars {
            chunks: self.raw.chunks_exact(2),
            _endian: self._endian,
        }
    }

    /// Returns and iterator over the [char]s of a string slice and their positions.
    #[inline]
    pub fn char_indices(&self) -> WStrCharIndices<E> {
        WStrCharIndices {
            chars: self.chars(),
            index: 0,
        }
    }

    /// Returns the [WStr] as a new owned [String].
    pub fn to_utf8(&self) -> String {
        self.chars().collect()
    }

    /// Returns `true` if all characters in the string are ASCII.
    #[inline]
    pub fn is_ascii(&self) -> bool {
        self.as_bytes().is_ascii()
    }
}

/// Iterator yielding `char` from a UTF-16 little-endian encoded byte slice.
///
/// The slice must contain valid UTF-16, otherwise this may panic or cause undefined
/// behaviour.
#[derive(Debug)]
pub struct WStrChars<'a, E: 'static + ByteOrder> {
    chunks: ChunksExact<'a, u8>,
    _endian: PhantomData<&'static E>,
}

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
            Some(unsafe { std::char::from_u32_unchecked(u as u32) })
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
            Some(unsafe { std::char::from_u32_unchecked(u as u32) })
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

/// Iterator yielding `(index, char)` tuples from a UTF-16 little-endian encoded byte slice.
///
/// The slice must contain valid UTF-16, otherwise this may panic or cause undefined
/// behaviour.
#[derive(Debug)]
pub struct WStrCharIndices<'a, E: 'static + ByteOrder> {
    chars: WStrChars<'a, E>,
    index: usize,
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
        self.index += c.len_utf16() * std::mem::size_of::<u16>();
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
        let pos = self.index + self.chars.chunks.len() * std::mem::size_of::<u16>();
        Some((pos, c))
    }
}

impl<'a, E> FusedIterator for WStrCharIndices<'a, E> where E: ByteOrder {}

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
fn is_leading_surrogate(code_unit: u16) -> bool {
    code_unit & 0xD800 == 0xD800
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
fn is_trailing_surrogate(code_unit: u16) -> bool {
    code_unit & 0xDC00 == 0xDC00
}

/// Decodes a surrogate pair of code units into a char.
///
/// This results in undefined behaviour if the code units do not form a valid surrogate
/// pair.
#[inline]
unsafe fn decode_surrogates(u: u16, u2: u16) -> char {
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
    unsafe { std::char::from_u32_unchecked(c) }
}

/// Checks that the raw bytes are valid UTF-16LE.
fn validate_raw_utf16<E: ByteOrder>(raw: &[u8]) -> Result<(), Utf16Error> {
    // This could be optimised as it does not need to be actually decoded, just needs to
    // be a valid byte sequence.
    if raw.len() % 2 != 0 {
        return Err(Utf16Error::new());
    }
    let u16iter = raw.chunks_exact(2).map(|chunk| E::read_u16(chunk));
    if std::char::decode_utf16(u16iter).all(|result| result.is_ok()) {
        Ok(())
    } else {
        Err(Utf16Error::new())
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
    fn test_wstr_chars() {
        let b = b"h\x00e\x00l\x00l\x00o\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);

        let b = b"\x00\xd8\x00\xdcx\x00";
        let s = WStr::from_utf16le(b).unwrap();
        let chars: Vec<char> = s.chars().collect();
        assert_eq!(chars, vec!['\u{10000}', 'x']);
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
