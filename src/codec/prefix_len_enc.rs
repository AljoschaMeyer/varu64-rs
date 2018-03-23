use async_codec::{AsyncEncode, AsyncEncodeLen, PollEnc};
use async_codec_util::encoder::{chain as enc_chain, Chain as EncChain};
use futures_core::task::Context;
use futures_io::AsyncWrite;

use super::super::Encode;

/// Wraps an `AsyncEncodeLen`, returning a new encoder that prepends the length of the inner
/// encoder, than encodes it.
pub struct PrefixLenEnc<C>(EncChain<Encode, C>);

impl<C> PrefixLenEnc<C>
    where C: AsyncEncodeLen
{
    /// Create a new `PrefixLenEnc` that runs the inner encoder prefixed by its length as a VarU64.
    pub fn new(inner: C) -> PrefixLenEnc<C> {
        PrefixLenEnc(enc_chain(Encode::new(inner.remaining_bytes() as u64), inner))
    }
}

impl<C> AsyncEncode for PrefixLenEnc<C>
    where C: AsyncEncodeLen
{
    fn poll_encode<W: AsyncWrite>(self, cx: &mut Context, writer: &mut W) -> PollEnc<Self> {
        match self.0.poll_encode(cx, writer) {
            PollEnc::Done(written) => PollEnc::Done(written),
            PollEnc::Progress(inner, written) => PollEnc::Progress(PrefixLenEnc(inner), written),
            PollEnc::Pending(inner) => PollEnc::Pending(PrefixLenEnc(inner)),
            PollEnc::Errored(err) => PollEnc::Errored(err),
        }
    }
}

impl<C> AsyncEncodeLen for PrefixLenEnc<C>
    where C: AsyncEncodeLen
{
    fn remaining_bytes(&self) -> usize {
        self.0.remaining_bytes()
    }
}
