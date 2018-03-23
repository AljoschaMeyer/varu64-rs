use async_codec::{AsyncDecode, DecodeError, PollDec};
use async_codec_util::decoder::{DecodeExact, DecodeExactError};
use futures_core::task::Context;
use futures_io::AsyncRead;

use super::super::Decode;

enum PrefixExactLenDecState<D> {
    Length(Decode, D),
    Decoding(DecodeExact<D>),
}

/// Wraps a decoder and first reads a VarU64 byte count, then continues with the wrapped decoder.
///
/// The new decoder errors if the wrapped decoder does not decode its item at exactly the read byte
/// count (which always happens if the read VarU64 is zero).
pub struct PrefixExactLenDec<D>(PrefixExactLenDecState<D>);

impl<D> PrefixExactLenDec<D> {
    /// Create a new `PrefixExactLenDec`, wrapping the given `dec`.
    pub fn new(dec: D) -> PrefixExactLenDec<D> {
        PrefixExactLenDec(PrefixExactLenDecState::Length(Decode::new(), dec))
    }
}

impl<D> AsyncDecode for PrefixExactLenDec<D>
    where D: AsyncDecode
{
    type Item = D::Item;
    type Error = DecodeExactError<D::Error, D::Item>;

    fn poll_decode<R: AsyncRead>(mut self,
                                 cx: &mut Context,
                                 reader: &mut R)
                                 -> PollDec<Self::Item, Self, Self::Error> {
        match self.0 {
            PrefixExactLenDecState::Length(len_dec, inner) => {
                match len_dec.poll_decode(cx, reader) {
                    PollDec::Done(len, read) => {
                        self.0 = PrefixExactLenDecState::Decoding(DecodeExact::new(inner,
                                                                                   len as usize));
                        PollDec::Progress(self, read)
                    }
                    PollDec::Progress(len_dec, read) => {
                        self.0 = PrefixExactLenDecState::Length(len_dec, inner);
                        debug_assert!(false);
                        PollDec::Progress(self, read)
                    }
                    PollDec::Pending(len_dec) => {
                        self.0 = PrefixExactLenDecState::Length(len_dec, inner);
                        PollDec::Pending(self)
                    }
                    PollDec::Errored(err) => {
                        match err {
                            DecodeError::ReaderError(reader_err) => {
                                PollDec::Errored(DecodeError::ReaderError(reader_err))
                            }
                            DecodeError::DataError(_) => unreachable!(),
                        }
                    }
                }
            }
            PrefixExactLenDecState::Decoding(inner) => {
                match inner.poll_decode(cx, reader) {
                    PollDec::Done(item, read) => PollDec::Done(item, read),
                    PollDec::Progress(inner, read) => {
                        self.0 = PrefixExactLenDecState::Decoding(inner);
                        PollDec::Progress(self, read)
                    }
                    PollDec::Pending(inner) => {
                        self.0 = PrefixExactLenDecState::Decoding(inner);
                        PollDec::Pending(self)
                    }
                    PollDec::Errored(err) => PollDec::Errored(err),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::PrefixLenEnc;

    use std::io::Cursor;

    use async_codec_util::decode;
    use async_codec_util::testing::{test_codec_len, unexpected_eof_errors};
    use futures_executor::block_on;
    use futures_util::io::AllowStdIo;

    use atm_io_utils::partial::*;
    use async_ringbuffer::ring_buffer;
    use async_byteorder::{decode_i64_native, encode_i64_native};

    quickcheck! {
        fn prefix_exact_len(buf_size: usize, read_ops: Vec<PartialOp>, write_ops: Vec<PartialOp>, num: i64) -> bool {
            let mut read_ops = read_ops;
            let mut write_ops = write_ops;
            let (w, r) = ring_buffer(buf_size + 1);
            let w = PartialWrite::new(w, write_ops.drain(..));
            let r = PartialRead::new(r, read_ops.drain(..));

            let test_outcome = test_codec_len(r, w, PrefixExactLenDec::new(decode_i64_native()), PrefixLenEnc::new(encode_i64_native(num)));
            test_outcome.1 && test_outcome.0 == num
        }
    }

    #[test]
    fn decode_exact_len_early() {
        let reader = AllowStdIo::new(Cursor::new([0b0000_0010, 0b0000_0000]));
        let dec = PrefixExactLenDec::new(Decode::new());
        let expected_err = block_on(decode(reader, dec)).unwrap_err();

        match expected_err {
            (_, DecodeError::DataError(DecodeExactError::Early(0, 1))) => {}
            other => panic!("should emit EcodeExactError::Early, got: {:?}", other),
        }
    }

    #[test]
    fn decode_exact_len_late() {
        let reader = AllowStdIo::new(Cursor::new([0b0000_0001, 0b1000_0000, 0b0000_0001]));
        let dec = PrefixExactLenDec::new(Decode::new());

        assert!(unexpected_eof_errors(reader, dec));
    }
}
