//! Implementations for [`Utf16Error`].

use std::fmt;

use crate::Utf16Error;

impl fmt::Display for Utf16Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Invalid UTF-16LE data in byte slice")
    }
}

impl std::error::Error for Utf16Error {}

impl Utf16Error {
    /// Returns the index in given bytes up to which valid UTF-16 was verified.
    pub fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }

    /// Return the length of the error if it is recoverable.
    ///
    ///  - `None`: the end of the input was reached unexpectedly.
    ///    [`Utf16Error::valid_up_to`] is 1 to 3 bytes from the end of the input.  If a byte
    ///    stream such as a file or a network socket is being decoded incrementally, this
    ///    could still be a valid char whose byte sequence is spanning multiple chunks.
    ///
    /// - `Some(len)`: an unexpected byte was encountered.  The length provided is that of
    ///   the invalid byte sequence that starts at the index given by
    ///   [`Utf16Error::valid_up_to`].  Decoding should resume after that sequence (after
    ///   inserting a [`U+FFFD REPLACEMENT CHARACTER`](std::char::REPLACEMENT_CHARACTER)) in
    ///   case of lossy decoding.  In fact for UTF-16 the `len` reported here will always be
    ///   exactly 2 since this never looks ahead to see if the bytes following the error
    ///   sequence are valid as well as otherwise you would not know how many replacement
    ///   characters to insert when writing a lossy decoder.
    ///
    /// The semantics of this API are compatible with the semantics of
    /// [`Utf8Error`](std::str::Utf8Error).
    pub fn error_len(&self) -> Option<usize> {
        self.error_len.map(|len| len.into())
    }
}
