//! Micro benchmarks
//!
//! Run with `cargo +nightly bench`.

#![feature(test)]

extern crate test;

use test::Bencher;

use byteorder::{ByteOrder, LE};

#[bench]
fn bench_encode_char_stdlib(b: &mut Bencher) {
    let mut vec = Vec::new();
    let chars = vec![
        'h',
        '\u{10000}',
        'e',
        '\u{10001}',
        'l',
        '\u{10002}',
        'l',
        '\u{10003}',
        'o',
        '\u{10004}',
    ];

    b.iter(|| {
        for ch in chars.iter().copied() {
            let mut buf_u16 = [0u16; 2];
            let code_units = ch.encode_utf16(&mut buf_u16);
            let byte_count = code_units.len() * core::mem::size_of::<u16>();
            let mut buf = [0u8; 4];
            LE::write_u16_into(code_units, &mut buf[..byte_count]);
            vec.extend_from_slice(&buf[..byte_count]);
        }
    });
}

#[bench]
fn bench_encode_char_manual(b: &mut Bencher) {
    let mut vec = Vec::new();
    let chars = vec![
        'h',
        '\u{10000}',
        'e',
        '\u{10001}',
        'l',
        '\u{10002}',
        'l',
        '\u{10003}',
        'o',
        '\u{10004}',
    ];

    b.iter(|| {
        for ch in chars.iter().copied() {
            let mut buf = [0u8; 4];
            let mut code_point: u32 = ch.into();
            if (code_point & 0xFFFF) == code_point {
                LE::write_u16(&mut buf, code_point as u16);
                vec.extend_from_slice(&buf[..2]);
            } else {
                code_point -= 0x1_0000;
                let code_unit0: u16 = 0xD800 | ((code_point >> 10) as u16);
                let code_unit1: u16 = 0xDC00 | ((code_point as u16) & 0x3FF);
                LE::write_u16(&mut buf, code_unit0);
                LE::write_u16(&mut buf[2..], code_unit1);
                vec.extend_from_slice(&buf);
            }
        }
    });
}

#[bench]
fn bench_encode_char_manual_with_panic(b: &mut Bencher) {
    let mut vec = Vec::new();
    let chars = vec![
        'h',
        '\u{10000}',
        'e',
        '\u{10001}',
        'l',
        '\u{10002}',
        'l',
        '\u{10003}',
        'o',
        '\u{10004}',
    ];

    b.iter(|| {
        for ch in chars.iter().copied() {
            let mut buf = [0u8; 4];
            let mut code_point: u32 = ch.into();
            if (code_point & 0xFFFF) == code_point {
                assert!(buf.len() >= 2, "destination too small, need 2 bytes");
                LE::write_u16(&mut buf, code_point as u16);
                vec.extend_from_slice(&buf[..2]);
            } else {
                assert!(buf.len() >= 4, "destination too small, need 4 bytes");
                code_point -= 0x1_0000;
                let code_unit0: u16 = 0xD800 | ((code_point >> 10) as u16);
                let code_unit1: u16 = 0xDC00 | ((code_point as u16) & 0x3FF);
                LE::write_u16(&mut buf, code_unit0);
                LE::write_u16(&mut buf[2..], code_unit1);
                vec.extend_from_slice(&buf);
            }
        }
    });
}
