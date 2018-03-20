//! A variable length encoding of u64 integers, based on [multiformats varints](https://github.com/multiformats/unsigned-varint/blob/8a6574bd229d9e158dad43acbcea7763b7807362/README.md),
//! but using the most significant bit of a 9-byte encoded integer to encode the most significant
//! bit of a u64 rather than using it a a continuation bit.
#![deny(missing_docs)]

extern crate async_codec;
#[macro_use(retry, read_nz, write_nz)]
extern crate atm_io_utils;
#[macro_use(try_ready)]
extern crate futures_core;
extern crate futures_io;
extern crate async_codec_util;

#[cfg(test)]
extern crate async_ringbuffer;
#[cfg(test)]
extern crate futures_util;
#[cfg(test)]
extern crate futures_executor;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck;

use std::io::{Read, Write, Error, Result as IoResult};
use std::io::ErrorKind::{UnexpectedEof, WriteZero};
use std::marker::PhantomData;
use std::u64::MAX as MAX_U64;

use async_codec::{AsyncEncode, AsyncEncodeLen, AsyncDecode, DecodeError, PollEnc, PollDec};
use async_codec_util::encoder::{chain as enc_chain, Chain as EncChain};
use futures_core::{Poll, Never};
use futures_core::Async::{Ready, Pending};
use futures_core::task::Context;
use futures_io::{AsyncRead, AsyncWrite, Error as FutIoErr, ErrorKind};

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

/// An `AsyncDecode` for decoding a VarU64.
pub struct Decode<R> {
    decoded: u64,
    offset: u8,
    shift_by: u8,
    _r: PhantomData<R>,
}

impl<R> Decode<R> {
    /// Create a new `Decode`r for decoding a VarU64.
    pub fn new() -> Decode<R> {
        Decode {
            decoded: 0,
            offset: 0,
            shift_by: 0,
            _r: PhantomData,
        }
    }
}

impl<R: AsyncRead> AsyncDecode<R> for Decode<R> {
    type Item = u64;
    type Error = Never;

    fn poll_decode(mut self,
                   cx: &mut Context,
                   reader: &mut R)
                   -> PollDec<Self::Item, Self, Self::Error> {
        let mut byte = [0u8];

        match reader.poll_read(cx, &mut byte) {
            Ok(Ready(0)) => {
                PollDec::Errored(FutIoErr::new(ErrorKind::UnexpectedEof, "VarU64").into())
            }
            Ok(Ready(_)) => {
                self.offset += 1;

                if byte[0] < 0b1000_0000 || self.offset == 9 {
                    PollDec::Done(self.decoded | (byte[0] as u64) << self.shift_by, 1)
                } else {
                    self.decoded |= ((byte[0] & 0b0111_1111) as u64) << self.shift_by;
                    self.shift_by += 7;
                    PollDec::Progress(self, 1)
                }
            }
            Ok(Pending) => PollDec::Pending(self),
            Err(err) => PollDec::Errored(err.into()),
        }
    }
}

/// An `AsyncEncode` for encoding a VarU64.
pub struct Encode<W> {
    int: u64,
    offset: u8,
    _w: PhantomData<W>,
}

impl<W> Encode<W> {
    /// Create a new `Encode`r for dencoding a VarU64.
    pub fn new(int: u64) -> Encode<W> {
        Encode {
            int,
            offset: 0,
            _w: PhantomData,
        }
    }
}

impl<W: AsyncWrite> AsyncEncode<W> for Encode<W> {
    fn poll_encode(mut self, cx: &mut Context, writer: &mut W) -> PollEnc<Self> {
        if self.int >= 0b1000_0000 && self.offset < 8 {
            match writer.poll_write(cx, &[(self.int as u8) | 0b1000_0000]) {
                Ok(Ready(0)) => {
                    PollEnc::Errored(FutIoErr::new(ErrorKind::WriteZero, "VarU64").into())
                }
                Ok(Ready(_)) => {
                    self.int >>= 7;
                    self.offset += 1;
                    PollEnc::Progress(self, 1)
                }
                Ok(Pending) => PollEnc::Pending(self),
                Err(err) => PollEnc::Errored(err),
            }
        } else {
            match writer.poll_write(cx, &[(self.int as u8)]) {
                Ok(Ready(0)) => {
                    PollEnc::Errored(FutIoErr::new(ErrorKind::WriteZero, "VarU64").into())
                }
                Ok(Ready(_)) => PollEnc::Done(1),
                Ok(Pending) => PollEnc::Pending(self),
                Err(err) => PollEnc::Errored(err),
            }
        }
    }
}

impl<W: AsyncWrite> AsyncEncodeLen<W> for Encode<W> {
    fn remaining_bytes(&self) -> usize {
        if self.offset == 9 {
            0
        } else {
            len(self.int) as usize
        }
    }
}

// /// Wraps an `AsyncEncodeLen`, returning a new encoder that prepends the length of the inner
// /// encoder, than encodes it.
// pub struct PrefixLenEnc<W, C>(EncChain<W, Encode<W>, C>);
//
// impl<W, C> PrefixLenEnc<W, C>
//     where W: AsyncWrite,
//           C: AsyncEncodeLen<W>
// {
//     /// Create a new `PrefixLenEnc` that runs the inner encoder prefixed by its length as a VarU64.
//     pub fn new(inner: C) -> PrefixLenEnc<W, C> {
//         PrefixLenEnc(enc_chain(Encode::new(inner.remaining_bytes() as u64), inner))
//     }
// }
//
// impl<W, C> AsyncEncode<W> for PrefixLenEnc<W, C>
//     where W: AsyncWrite,
//           C: AsyncEncodeLen<W>
// {
//     fn poll_encode(&mut self, cx: &mut Context, writer: &mut W) -> Poll<usize, FutIoErr> {
//         self.0.poll_encode(cx, writer)
//     }
// }
//
// impl<W, C> AsyncEncodeLen<W> for PrefixLenEnc<W, C>
//     where W: AsyncWrite,
//           C: AsyncEncodeLen<W>
// {
//     fn remaining_bytes(&self) -> usize {
//         self.0.remaining_bytes()
//     }
// }

// TODO move to atm-io-utils
/// Wraps a reader and limits the number of bytes that can be read from it. Once the limit has been
/// reached, further calls to poll_read will return `Ok(Ready(0))`.
pub struct LimitedReader<R> {
    inner: R,
    remaining: usize,
}

impl<R> LimitedReader<R> {
    /// Create a new `LimitedReader`, wrapping the given reader.
    pub fn new(inner: R, limit: usize) -> LimitedReader<R> {
        LimitedReader {
            inner: inner,
            remaining: limit,
        }
    }
}

impl<R: AsyncRead> AsyncRead for LimitedReader<R> {
    fn poll_read(&mut self, cx: &mut Context, buf: &mut [u8]) -> Poll<usize, Error> {
        self.inner.poll_read(cx, &mut buf[..self.remaining])
    }
}

// // TODO move to async-codec-util
// // TODO rename to State
// enum AndThenState<S, T, F> {
//     First(S, F),
//     Second(T),
// }
//
// /// TODO doc
// pub struct AndThen<R, S, T, F>(AndThenState<S, T, F>, PhantomData<R>);
//
// impl<R, S, T, F> AndThen<R, S, T, F> {
//     /// TODO doc
//     pub fn new(first: S, f: F) -> AndThen<R, S, T, F> {
//         AndThen(Some(AndThenState::First(first, f)), PhantomData)
//     }
// }
//
// impl<R, S, T, F> AsyncDecode<R> for AndThen<R, S, T, F>
//     where R: AsyncRead,
//           S: AsyncDecode<R>,
//           T: AsyncDecode<R, Error = S::Error>,
//           F: FnOnce(S::Item) -> T
// {
//     type Item = T::Item;
//     type Error = T::Error;
//
//     fn poll_decode(mut self,
//                    cx: &mut Context,
//                    reader: &mut R)
//                    -> PollDec<Self::Item, Self, Self::Error> {
//         match self.0 {
//             AndThenState::First(first, f) => {
//                 match first.poll_decode(cx, reader) {
//                     Done(item, read) => {
//                         self.0 = AndThenState::Second(f(item));
//                         Progress(self, read)
//                     },
//                     Progress(first, read) => {
//                         self.0 = AndThenState::First(first, f);
//                         Progress(self, read)
//                     }
//                     Pending(first) => {
//                         self.0 = AndThenState::First(first, f);
//                         Pending(self)
//                     }
//                     Errored(err) => Errored(err),
//                 }
//             }
//             AndThenState::Second(second) => {
//                 match second.poll_decode(cx, reader) {
//                     Done(item, read) => {
//                         Done(item, read)
//                     },
//                     Progress(second, read) => {
//                         self.0 = AndThenState::Second(second);
//                         Progress(self, read)
//                     }
//                     Pending(second) => {
//                         self.0 = AndThenState::Second(second);
//                         Pending(self)
//                     }
//                     Errored(err) => Errored(err),
//                 }
//             }
//         }
//     }
// }

// TODO instead of wrapping, take a FnOnce which receives the length as an arg. TODO turn that into a trait?
/// Wraps an `AsyncDecode`, returning a new decoder that first reads a VarU64 and then continues
/// with the wrapped decoder.
///
/// The new decoder errors if the wrapped decoder does not decode its item at exactly the right
/// byte count.
// pub struct PrefixLenDec {}

// TODO test len prefixing
#[cfg(test)]
mod tests {
    use super::*;

    use std::io::Cursor;

    use async_codec_util::{decode, encode};
    use async_codec_util::testing::{test_codec_len, unexpected_eof_errors, write_zero_errors};
    use futures_executor::block_on;
    use futures_util::io::AllowStdIo;

    use quickcheck::{Arbitrary, Gen};
    use atm_io_utils::partial::*;
    use async_ringbuffer::ring_buffer;

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
    fn decode_async_data() {
        for data in TESTDATA.iter() {
            let (_, decoded, len) =
                block_on(decode(AllowStdIo::new(Cursor::new(data.0)), Decode::new())).unwrap();
            assert_eq!(decoded, data.1);
            assert_eq!(len, data.0.len());
        }
    }

    #[test]
    fn decode_async_special() {
        // Missing data is an error
        assert!(unexpected_eof_errors(AllowStdIo::new(Cursor::new([0b1000_0000])), Decode::new()));
    }

    #[test]
    fn encode_async_data() {
        for data in TESTDATA.iter() {
            let (writer, len) = block_on(encode(AllowStdIo::new(vec![]), Encode::new(data.1)))
                .unwrap();
            assert_eq!(len, data.0.len());
            assert_eq!(&writer.into_inner()[..data.0.len()], data.0);
        }
    }

    #[test]
    fn encode_async_special() {
        let mut buf = [];
        assert!(write_zero_errors(AllowStdIo::new(Cursor::new(&mut buf[..])), Encode::new(0)));

        let mut buf = [];
        assert!(write_zero_errors(AllowStdIo::new(Cursor::new(&mut buf[..])), Encode::new(128)));

        let mut buf = [42u8];
        assert!(write_zero_errors(AllowStdIo::new(Cursor::new(&mut buf[..])), Encode::new(128)));
    }

    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    struct VarU64(u64);

    // Ignores `g.size()` and generates u64s of arbitrary size.
    impl Arbitrary for VarU64 {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            VarU64(g.next_u64())
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(VarU64))
        }
    }

    quickcheck! {
        fn codec(buf_size: usize, read_ops: Vec<PartialOp>, write_ops: Vec<PartialOp>, int: VarU64) -> bool {
            let mut read_ops = read_ops;
            let mut write_ops = write_ops;
            let (w, r) = ring_buffer(buf_size + 1);
            let w = PartialWrite::new(w, write_ops.drain(..));
            let r = PartialRead::new(r, read_ops.drain(..));

            let test_outcome = test_codec_len(r, w, Decode::new(), Encode::new(int.0));
            test_outcome.1 && VarU64(test_outcome.0) == int
        }
    }
}
