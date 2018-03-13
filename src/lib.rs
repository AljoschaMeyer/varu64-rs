//! A variable length encoding of u64 integers, based on [multiformats varints](https://github.com/multiformats/unsigned-varint/blob/8a6574bd229d9e158dad43acbcea7763b7807362/README.md),
//! but using the most significant bit of a 9-byte encoded integer to encode the most significant
//! bit of a u64 rather than using it a a continuation bit.
#![deny(missing_docs)]

extern crate futures_core;
extern crate futures_io;

use std::io::{Read, Write, Result as IoResult};
use std::u64::MAX as MAX_U64;

use futures_core::{Future, Poll};
use futures_core::task::Context;
use futures_io::{AsyncRead, AsyncWrite, Error as FutError};

/// The largest number of bytes an encoding can consume.
pub const MAX_LENGTH: u8 = 9;

/// The largest u64 that fits into one byte of encoding: 2u64.pow(7 * 1) - 1
pub const MAX_1: u64 = 127;

/// The largest u64 that fits into two bytes of encoding: 2u64.pow(7 * 2) - 1
pub const MAX_2: u64 = 16383;

/// The largest u64 that fits into three bytes of encoding: 2u64.pow(7 * 3) - 1
pub const MAX_3: u64 = 2097151;

/// The largest u64 that fits into four bytes of encoding: 2u64.pow(7 * 4) - 1
pub const MAX_4: u64 = 268435455;

/// The largest u64 that fits into five bytes of encoding: 2u64.pow(7 * 5) - 1
pub const MAX_5: u64 = 34359738367;

/// The largest u64 that fits into six bytes of encoding: 2u64.pow(7 * 6) - 1
pub const MAX_6: u64 = 4398046511103;

/// The largest u64 that fits into seven bytes of encoding: 2u64.pow(7 * 7) - 1
pub const MAX_7: u64 = 562949953421311;

/// The largest u64 that fits into eight bytes of encoding: 2u64.pow(7 * 8) - 1
pub const MAX_8: u64 = 72057594037927935;

/// The largest u64 that fits into nine bytes of encoding.
pub const MAX_9: u64 = MAX_U64;

/// Return the number of bytes needed to encode the given u64.
pub fn len(int: u64) -> u8 {
    // Could use base-7-ogarithms (rounded up) to actually compute this.
    if int <= MAX_1 {
        1
    } else if int <= MAX_2 {
        2
    } else if int <= MAX_3 {
        3
    } else if int <= MAX_4 {
        4
    } else if int <= MAX_5 {
        5
    } else if int <= MAX_6 {
        6
    } else if int <= MAX_7 {
        7
    } else if int <= MAX_8 {
        8
    } else {
        9
    }
}

/// Try to decode from a slice of bytes.
///
/// Returns the decoded u64 on success (use `len` to find out how many bytes of the buffer where
/// read), or `None` if decoding failed because the slice was not long enough.
pub fn decode_bytes(bytes: &[u8]) -> Option<u64> {
    let mut decoded = 0;
    let mut shift_by = 0;

    for (offset, &byte) in bytes.iter().enumerate() {
        if byte < 0b1000_0000 || offset == 8 {
            println!("{:?}", (byte as u64) << shift_by);
            return Some(decoded | (byte as u64) << shift_by);
        } else {
            decoded |= ((byte & 0b0111_1111) as u64) << shift_by;
            shift_by += 7;
        }
    }

    return None;
}

/// Try to decode from a slice of bytes.
///
/// Returns the decoded u64 and how many bytes were read on success, or `None` if decoding failed
/// because the slice was not long enough.
pub fn decode_bytes_len(bytes: &[u8]) -> Option<(u64, u8)> {
    unimplemented!()
}

/// Try to encode into a slice of bytes.
pub fn encode_bytes(int: u64, bytes: &mut [u8]) -> Option<()> {
    unimplemented!()
}

/// Try to encode into a slice of bytes, returning the length of the encoding in bytes.
pub fn encode_bytes_len(int: u64, bytes: &mut [u8]) -> Option<u8> {
    unimplemented!()
}

/// Try to decode from a `Read`..
///
/// Propagates all errors from calling `read`, and yields an error of kind "UnexpectedEof" if a
/// call to `read` returns 0 even though the encoding indicates that more data should follow.
pub fn decode_reader<R: Read>(reader: R) -> IoResult<(u64, u8)> {
    unimplemented!()
}

/// Try to decode from a `Read`, returning how many bytes were read.
///
/// Propagates all errors from calling `read`, and yields an error of kind "UnexpectedEof" if a
/// call to `read` returns 0 even though the encoding indicates that more data should follow.
pub fn decode_reader_len<R: Read>(reader: R) -> IoResult<(u64, u8)> {
    unimplemented!()
}

/// Try to encode into a `Write`, flushing as needed, and returning how many bytes were written.
///
/// Propagates all errors from calling `write`, and yields an error of kind "WriteZero" if a
/// call to `write` returns 0 even though not all data has been written.
pub fn encode_writer<W: Write>(int: u64, writer: W) -> IoResult<u8> {
    unimplemented!()
}

/// A future for decoding a u64 from an `AsyncRead`.
pub struct Decode<R> {
    reader: Option<R>,
    decoded: u64,
    offset: u8,
}

impl<R> Decode<R> {
    /// Create a new `Decode` future for decoding form the given `R`.
    pub fn new(reader: R) -> Decode<R> {
        Decode {
            reader: Some(reader),
            decoded: 0,
            offset: 0,
        }
    }
}

impl<R: AsyncRead> Future for Decode<R> {
    /// The decoded `u64`, and how many bytes were read decoding it.
    type Item = (u64, u8);
    /// Propagated from reading, or an error of kind "UnexpectedEof" if a call to `poll_read`
    /// returned 0 even though the encoding indicates that more data should follow.
    type Error = FutError;

    fn poll(&mut self, cx: &mut Context) -> Poll<Self::Item, Self::Error> {
        unimplemented!()
    }
}

/// A future for encoding a u64 into an `AsyncWrite`.
pub struct Encode<W> {
    writer: Option<W>,
    int: u64,
    offset: u8,
}

impl<W> Encode<W> {
    /// Create a new `Encode` future for encoding the given `u64` into the given `W`.
    pub fn new(int: u64, writer: W) -> Encode<W> {
        Encode {
            writer: Some(writer),
            int,
            offset: 0,
        }
    }
}

impl<W: AsyncWrite> Future for Encode<W> {
    /// How many bytes were written into the `W`.
    type Item = u8;
    /// Propagated from writing, or an error of kind "WriteZero" if a call to `poll_write` returned
    /// 0 even though not all data has been written.
    type Error = FutError;

    fn poll(&mut self, cx: &mut Context) -> Poll<Self::Item, Self::Error> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_bytes() {
        assert_eq!(decode_bytes(&[0b0000_0000]), Some(0));
        assert_eq!(decode_bytes(&[0b0000_0001]), Some(1));
        assert_eq!(decode_bytes(&[0b0111_1111]), Some(127));
        assert_eq!(decode_bytes(&[0b1000_0000, 0b0000_0001]), Some(128));
        assert_eq!(decode_bytes(&[0b1111_1111, 0b0000_0001]), Some(255));
        assert_eq!(decode_bytes(&[0b1010_1100, 0b0000_0010]), Some(300));
        assert_eq!(decode_bytes(&[0b1000_0000, 0b1000_0000, 0b0000_0001]),
                   Some(16384));
        assert_eq!(decode_bytes(&[0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b0000_0001]),
                   Some(2u64.pow(56)));
        assert_eq!(decode_bytes(&[0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000,
                                  0b1000_0000]),
                   Some(2u64.pow(63)));
        assert_eq!(decode_bytes(&[0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111]),
                   Some(MAX_U64));

        // Trailing data is ok
        assert_eq!(decode_bytes(&[0b0000_0000, 42]), Some(0));

        // Missing data is an error
        assert_eq!(decode_bytes(&[0b1000_0000]), None);

        // Continuation followed by 0 is ok.
        assert_eq!(decode_bytes(&[0b1000_0000, 0b0000_0000]), Some(0));
        assert_eq!(decode_bytes(&[0b1000_0000, 0b1000_0000, 0b0000_0000]),
                   Some(0));
    }
}

// TODO test everything
