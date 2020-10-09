# UTF-16 string types

This crate provides two string types to work with UTF-16 encoded
bytes, they are directly analogous to how `String` and `&str` work
with UTF-8 encoded bytes.

UTF-16 can be encoded in little- and big-endian byte order, this crate
identifies which encoding the types contain to using a generic
[byteorder](https://docs.rs/byteorder) type, thus the main types
exposed are:

- `&WStr<ByteOrder>`
- `WString<ByteOrder>`

These types aim to behave very similar to the standard libarary `&str`
and `String` types.  While many APIs are already covered, feel free to
contribute more methods.
