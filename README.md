# UTF-16 string types

This crate provides string types to work with UTF-16 encoded bytes, in
a similar way to which `&str` and `String` works with UTF-8 encoded
bytes.

```
use wstring::{WStr, LittleEndian};

let b = b"h\x00e\x00l\x00l\x00o\x00";
let s: &WStr<LittleEndian> = WStr::from_utf16(b).unwrap();

let chars: Vec<char> = s.chars().collect();
assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);

assert_eq!(s.to_utf8(), "hello");
```

Still a work in progress so far, but already usable.
