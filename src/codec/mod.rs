//! Encoders and decoders using VarU64s.

mod prefix_len_enc;
pub use self::prefix_len_enc::PrefixLenEnc;
mod prefix_exact_len_dec;
pub use self::prefix_exact_len_dec::PrefixExactLenDec;
