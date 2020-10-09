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

use std::marker::PhantomData;
use std::slice::ChunksExact;

use byteorder::ByteOrder;

pub use byteorder::{BigEndian, LittleEndian, BE, LE};

mod error;
mod iters;
mod slicing;
mod utf16;
mod wstr;
mod wstring;

#[doc(inline)]
pub use crate::slicing::SliceIndex;

/// Error for invalid UTF-16 encoded bytes.
#[derive(Debug, Copy, Clone)]
pub struct Utf16Error {
    valid_up_to: usize,
    error_len: Option<u8>,
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

/// Iterator yielding `char` from a UTF-16 encoded byte slice.
///
/// The slice must contain valid UTF-16, otherwise this may panic or cause undefined
/// behaviour.
#[derive(Debug)]
pub struct WStrChars<'a, E: 'static + ByteOrder> {
    chunks: ChunksExact<'a, u8>,
    _endian: PhantomData<&'static E>,
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
