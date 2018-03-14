//! A variable length encoding of u64 integers, based on [multiformats varints](https://github.com/multiformats/unsigned-varint/blob/8a6574bd229d9e158dad43acbcea7763b7807362/README.md),
//! but using the most significant bit of a 9-byte encoded integer to encode the most significant
//! bit of a u64 rather than using it a a continuation bit.
#![deny(missing_docs)]

// extern crate async_serialization;
#[macro_use(retry)]
extern crate atm_io_utils;
extern crate futures_core;
extern crate futures_io;
#[cfg(test)]
extern crate futures_util;
#[cfg(test)]
extern crate futures_executor;

use std::io::{Read, Write, Error, Result as IoResult};
use std::io::ErrorKind::{UnexpectedEof, WriteZero};
use std::u64::MAX as MAX_U64;

// use async_serialization::{AsyncSerialize, AsyncWriterFuture, AsyncWriterFutureLen,
//                           AsyncSerializeLen};
use futures_core::{Future, Poll};
use futures_core::Async::{Ready, Pending};
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
/// Returns the decoded u64 and how many bytes were read on success, or `None` if decoding failed
/// because the slice was not long enough.
pub fn decode_bytes(bytes: &[u8]) -> Option<(u64, u8)> {
    let mut decoded = 0;
    let mut shift_by = 0;

    for (offset, &byte) in bytes.iter().enumerate() {
        if byte < 0b1000_0000 || offset == 8 {
            return Some((decoded | (byte as u64) << shift_by, (offset + 1) as u8));
        } else {
            decoded |= ((byte & 0b0111_1111) as u64) << shift_by;
            shift_by += 7;
        }
    }

    return None;
}

/// Try to encode into a slice of bytes, returning the length of the encoding in bytes.
///
/// Returns `None` if the given buffer is not big enough.
pub fn encode_bytes(mut int: u64, bytes: &mut [u8]) -> Option<u8> {
    let mut offset = 0;

    while int >= 0b1000_0000 && offset < 8 {
        match bytes.get_mut(offset) {
            Some(ptr) => {
                *ptr = (int as u8) | 0b1000_0000;
            }
            None => {
                return None;
            }
        }
        int >>= 7;
        offset += 1;
    }

    match bytes.get_mut(offset) {
        Some(ptr) => {
            *ptr = int as u8;
            Some((offset + 1) as u8)
        }
        None => None,
    }
}

/// Try to decode from a `Read`, returning how many bytes were read.
///
/// Propagates all errors from calling `read`, and yields an error of kind "UnexpectedEof" if a
/// call to `read` returns 0 even though the encoding indicates that more data should follow.
pub fn decode_reader<R: Read>(reader: &mut R) -> IoResult<(u64, u8)> {
    let mut decoded = 0;
    let mut shift_by = 0;
    let mut byte = [0u8];

    for i in 0..9 {
        let read = reader.read(&mut byte)?;

        if read == 0 {
            return Err(Error::new(UnexpectedEof, "Failed to read varu64"));
        } else {
            if byte[0] < 0b1000_0000 || i == 8 {
                return Ok((decoded | (byte[0] as u64) << shift_by, (i + 1) as u8));
            } else {
                decoded |= ((byte[0] & 0b0111_1111) as u64) << shift_by;
                shift_by += 7;
            }
        }
    }

    unreachable!()
}

/// Try to encode into a `Write`, returning how many bytes were written.
///
/// Propagates all errors from calling `write` except `Interruped` errors, and yields an error of
/// kind "WriteZero" if a call to `write` returns 0 even though not all data has been written.
pub fn encode_writer<W: Write>(mut int: u64, writer: &mut W) -> IoResult<u8> {
    let mut offset = 0;

    while int >= 0b1000_0000 && offset < 8 {
        if retry!(writer.write(&[(int as u8) | 0b1000_0000])) == 0 {
            return Err(Error::new(WriteZero, "Failed to write varu64"));
        } else {
            int >>= 7;
            offset += 1;
        }
    }

    if retry!(writer.write(&[int as u8])) == 0 {
        return Err(Error::new(WriteZero, "Failed to write varu64"));
    } else {
        return Ok((offset + 1) as u8);
    }
}

/// A future for decoding a u64 from an `AsyncRead`.
pub struct Decode<R> {
    reader: Option<R>,
    decoded: u64,
    i: u8,
    shift_by: u8,
}

impl<R> Decode<R> {
    /// Create a new `Decode` future for decoding from the given `R`.
    pub fn new(reader: R) -> Decode<R> {
        Decode {
            reader: Some(reader),
            decoded: 0,
            i: 0,
            shift_by: 0,
        }
    }
}

impl<R: AsyncRead> Future for Decode<R> {
    /// The wrapped reader, the decoded `u64`, and how many bytes were read decoding it.
    type Item = (R, u64, usize);
    /// Propagated from reading, or an error of kind "UnexpectedEof" if a call to `poll_read`
    /// returned 0 even though the encoding indicates that more data should follow.
    type Error = (R, FutError);

    fn poll(&mut self, cx: &mut Context) -> Poll<Self::Item, Self::Error> {
        let mut reader = self.reader
            .take()
            .expect("Polled Decode future after completion");

        let mut byte = [0u8];

        match reader.poll_read(cx, &mut byte) {
            Ok(Ready(0)) => Err((reader, Error::new(UnexpectedEof, "Failed to read varu64"))),
            Ok(Ready(read)) => {
                debug_assert!(read == 1);
                if byte[0] < 0b1000_0000 || self.i == 8 {
                    Ok(Ready((reader,
                              self.decoded | (byte[0] as u64) << self.shift_by,
                              self.i as usize + 1)))
                } else {
                    self.decoded |= ((byte[0] & 0b0111_1111) as u64) << self.shift_by;
                    self.shift_by += 7;
                    self.i += 1;
                    self.reader = Some(reader);
                    self.poll(cx)
                }
            }
            Ok(Pending) => {
                self.reader = Some(reader);
                Ok(Pending)
            }
            Err(err) => Err((reader, err)),
        }
    }
}

// TODO impl async deserialization trait

/// A future for encoding a u64 into an `AsyncWrite`.
pub struct Encode<W> {
    writer: Option<W>,
    int: u64,
    offset: u8,
}

impl<W> Encode<W> {
    /// Create a new `Encode` future for encoding the given `u64` into the given `W`.
    pub fn new(writer: W, int: u64) -> Encode<W> {
        Encode {
            writer: Some(writer),
            int,
            offset: 0,
        }
    }
}

impl<W: AsyncWrite> Future for Encode<W> {
    /// The wrapped `W`, and how many bytes were written into the `W`.
    type Item = (W, usize);
    /// Propagated from writing, or an error of kind "WriteZero" if a call to `poll_write` returned
    /// 0 even though not all data has been written.
    type Error = (W, FutError);

    /// Note that this does not flush or close the wrapped `W`.
    fn poll(&mut self, cx: &mut Context) -> Poll<Self::Item, Self::Error> {
        let mut writer = self.writer
            .take()
            .expect("Polled Encode future after completion");

        if self.int >= 0b1000_0000 && self.offset < 8 {
            match writer.poll_write(cx, &[(self.int as u8) | 0b1000_0000]) {
                Ok(Ready(0)) => Err((writer, Error::new(WriteZero, "Failed to write varu64"))),
                Ok(Ready(written)) => {
                    debug_assert!(written == 1);
                    self.int >>= 7;
                    self.offset += 1;
                    self.writer = Some(writer);
                    self.poll(cx)
                }
                Ok(Pending) => Ok(Pending),
                Err(err) => Err((writer, err)),
            }
        } else {
            match writer.poll_write(cx, &[self.int as u8]) {
                Ok(Ready(0)) => Err((writer, Error::new(WriteZero, "Failed to write varu64"))),
                Ok(Ready(written)) => {
                    debug_assert!(written == 1);
                    Ok(Ready((writer, self.offset as usize + 1)))
                }
                Ok(Pending) => Ok(Pending),
                Err(err) => Err((writer, err)),
            }
        }
    }
}

// impl<W> AsyncWriterFuture<W> for Encode<W>
//     where W: AsyncWrite
// {
//     fn already_written(&self) -> usize {
//         self.1
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    use std::io::Cursor;

    use futures_executor::block_on;
    use futures_util::io::AllowStdIo;

    #[test]
    fn test_len() {
        assert_eq!(len(0), 1);
        assert_eq!(len(1), 1);
        assert_eq!(len(127), 1);
        assert_eq!(len(128), 2);
        assert_eq!(len(255), 2);
        assert_eq!(len(300), 2);
        assert_eq!(len(16384), 3);
        assert_eq!(len(2u64.pow(56)), 9);
        assert_eq!(len(2u64.pow(63)), 9);
        assert_eq!(len(MAX_U64), 9);
    }

    const TESTDATA: [(&[u8], u64); 10] = [(&[0b0000_0000], 0),
                                          (&[0b0000_0001], 1),
                                          (&[0b0111_1111], 127),
                                          (&[0b1000_0000, 0b0000_0001], 128),
                                          (&[0b1111_1111, 0b0000_0001], 255),
                                          (&[0b1010_1100, 0b0000_0010], 300),
                                          (&[0b1000_0000, 0b1000_0000, 0b0000_0001], 16384),
                                          (&[0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b0000_0001],
                                           72057594037927936), // 2u64.pow(56)
                                          (&[0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000,
                                             0b1000_0000],
                                           9223372036854775808), // 2u64.pow(63)
                                          (&[0b1111_1111,
                                             0b1111_1111,
                                             0b1111_1111,
                                             0b1111_1111,
                                             0b1111_1111,
                                             0b1111_1111,
                                             0b1111_1111,
                                             0b1111_1111,
                                             0b1111_1111],
                                           MAX_U64)];

    #[test]
    fn decode_bytes_data() {
        for data in TESTDATA.iter() {
            assert_eq!(decode_bytes(data.0), Some((data.1, data.0.len() as u8)));
        }
    }

    #[test]
    fn decode_bytes_special() {
        // Trailing data is ok
        assert_eq!(decode_bytes(&[0b0000_0000, 42]), Some((0, 1)));
        assert_eq!(decode_bytes(&[0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  0b1111_1111,
                                  42]),
                   Some((MAX_U64, 9)));

        // Missing data is an error
        assert_eq!(decode_bytes(&[0b1000_0000]), None);

        // Continuation followed by 0 is ok.
        assert_eq!(decode_bytes(&[0b1000_0000, 0b0000_0000]), Some((0, 2)));
        assert_eq!(decode_bytes(&[0b1000_0000, 0b1000_0000, 0b0000_0000]),
                   Some((0, 3)));
    }

    #[test]
    fn encode_bytes_data() {
        for data in TESTDATA.iter() {
            let mut buf = [42u8; 9];
            assert_eq!(encode_bytes(data.1, &mut buf).unwrap(), data.0.len() as u8);
            assert_eq!(&buf[..data.0.len()], data.0);

            for &byte in &buf[data.0.len()..] {
                assert_eq!(byte, 42u8);
            }
        }
    }

    #[test]
    fn encode_bytes_special() {
        let mut buf = [];
        assert!(encode_bytes(0, &mut buf).is_none());

        let mut buf = [];
        assert!(encode_bytes(128, &mut buf).is_none());

        let mut buf = [42u8];
        assert!(encode_bytes(128, &mut buf).is_none());
    }

    #[test]
    fn decode_reader_data() {
        for data in TESTDATA.iter() {
            assert_eq!(decode_reader(&mut Cursor::new(data.0)).unwrap(),
                       (data.1, data.0.len() as u8));
        }
    }

    #[test]
    fn decode_reader_special() {
        // Missing data is an error
        assert_eq!(decode_reader(&mut Cursor::new([0b1000_0000]))
                       .unwrap_err()
                       .kind(),
                   UnexpectedEof);
    }

    #[test]
    fn encode_writer_data() {
        for data in TESTDATA.iter() {
            let mut writer = vec![];

            assert_eq!(encode_writer(data.1, &mut writer).unwrap(),
                       data.0.len() as u8);
            assert_eq!(&writer[..data.0.len()], data.0);
        }
    }

    #[test]
    fn encode_writer_special() {
        let mut buf = [];
        assert_eq!(encode_writer(0, &mut Cursor::new(&mut buf[..]))
                       .unwrap_err()
                       .kind(),
                   WriteZero);

        let mut buf = [];
        assert_eq!(encode_writer(128, &mut Cursor::new(&mut buf[..]))
                       .unwrap_err()
                       .kind(),
                   WriteZero);

        let mut buf = [42u8];
        assert_eq!(encode_writer(128, &mut Cursor::new(&mut buf[..]))
                       .unwrap_err()
                       .kind(),
                   WriteZero);
    }

    #[test]
    fn decode_future_data() {
        for data in TESTDATA.iter() {
            let (_, decoded, len) = block_on(Decode::new(AllowStdIo::new(Cursor::new(data.0))))
                .unwrap();
            assert_eq!(decoded, data.1);
            assert_eq!(len, data.0.len());
        }
    }

    #[test]
    fn decode_future_special() {
        // Missing data is an error
        assert_eq!(block_on(Decode::new(AllowStdIo::new(Cursor::new([0b1000_0000]))))
                       .unwrap_err()
                       .1
                       .kind(),
                   UnexpectedEof);
    }

    #[test]
    fn encode_future_data() {
        for data in TESTDATA.iter() {
            let (writer, len) = block_on(Encode::new(AllowStdIo::new(vec![]), data.1)).unwrap();
            assert_eq!(len, data.0.len());
            assert_eq!(&writer.into_inner()[..data.0.len()], data.0);
        }
    }

    #[test]
    fn encode_future_special() {
        let mut buf = [];
        assert_eq!(block_on(Encode::new(AllowStdIo::new(Cursor::new(&mut buf[..])), 0))
                       .unwrap_err()
                       .1
                       .kind(),
                   WriteZero);

        let mut buf = [];
        assert_eq!(block_on(Encode::new(AllowStdIo::new(Cursor::new(&mut buf[..])), 128))
                       .unwrap_err()
                       .1
                       .kind(),
                   WriteZero);

        let mut buf = [42u8];
        assert_eq!(block_on(Encode::new(AllowStdIo::new(Cursor::new(&mut buf[..])), 128))
                       .unwrap_err()
                       .1
                       .kind(),
                   WriteZero);
    }
}
