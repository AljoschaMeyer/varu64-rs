//! Nonblocking encoding and decoding.

use super::encoding_length;

/// Everything that can go wrong when decoding data.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum DecodeError {
    /// The input was not encoded canonically.
    NonCanonical,
}

/// State for the nonblocking decoding.
pub struct Decoder {
    val: u64, // This accumulates parsed data until it contains the correct value.
    total_length: usize, // How many bytes does this varu64 take up in total? A value of 0 indicates the initial state.
    parsed: usize, // How many bytes have we parsed already?
}

impl Decoder {
    pub fn new() -> Decoder {
        Decoder {
            val: 0,
            total_length: 0,
            parsed: 0,
        }
    }

    /// Decode a VarU64 from the input. The decoder can be reused as many times as you want.
    ///
    /// Returns how many bytes have been written. A `None` is returned if more input is needed.
    pub fn decode(&mut self, input: &[u8]) -> (usize, Option<Result<u64, DecodeError>>) {
        self.do_decode(input, 0)
    }

    pub fn do_decode(&mut self,
                     input: &[u8],
                     total_consumed: usize)
                     -> (usize, Option<Result<u64, DecodeError>>) {
        if input.len() == 0 {
            return (0, None);
        }

        let b = input[0];

        if self.total_length == 0 {
            debug_assert!(self.val == 0);
            debug_assert!(self.parsed == 0);
            debug_assert!(total_consumed == 0);
            match b {
                0...247 => {
                    return (1, Some(Ok(b as u64)));
                }

                248 => {
                    self.total_length = 1;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                249 => {
                    self.total_length = 2;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                250 => {
                    self.total_length = 3;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                251 => {
                    self.total_length = 4;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                252 => {
                    self.total_length = 5;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                253 => {
                    self.total_length = 6;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                254 => {
                    self.total_length = 7;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                255 => {
                    self.total_length = 8;
                    return self.do_decode(&input[1..], total_consumed + 1);
                }

                _ => unreachable!(), // all 256 cases covered
            }
        } else {
            debug_assert!(self.total_length > self.parsed);

            self.val <<= 8;
            self.val += b as u64;

            self.parsed += 1;

            if self.parsed == self.total_length {
                if self.parsed > encoding_length(self.val) - 1 {
                    self.reset();
                    return (total_consumed + 1, Some(Err(DecodeError::NonCanonical)));
                } else {
                    self.reset();
                    return (total_consumed + 1, Some(Ok(self.val)));
                }
            } else {
                return self.decode(&input[1..]);
            }
        }
    }

    fn reset(&mut self) {
        self.val = 0;
        self.total_length = 0;
        self.parsed = 0;
    }
}

/// State for the nonblocking encoding.
pub struct Encoder {
    n: u64, // What to encode (or what remains of it).
    remaining: usize, // How many bytes do we still need to output? `9` signals that none have been output yet.
}

impl Encoder {
    /// Create an encoder for encoding the given number.
    pub fn new(n: u64) -> Encoder {
        Encoder { n, remaining: 9 }
    }

    /// Encode (potentially only parts of) the number into the output buffer. This returns how
    /// many bytes were written. If it returns zero even though the `out` buffer had non-zero
    /// length, the encoding process is done.
    pub fn encode(&mut self, out: &mut [u8]) -> usize {
        self.do_encode(out, 0)
    }

    fn do_encode(&mut self, out: &mut [u8], total_output: usize) -> usize {
        if out.len() == 0 {
            return 0;
        }

        if self.remaining == 0 {
            return 0;
        }

        if self.remaining == 9 {
            debug_assert!(total_output == 0);
            self.remaining = encoding_length(self.n) - 1;

            match self.remaining {
                0 => {
                    out[0] = self.n as u8;
                    return 1;
                }

                1 => {
                    out[0] = 248;
                    return self.do_encode(&mut out[1..], 1);
                }

                2 => {
                    out[0] = 249;
                    return self.do_encode(&mut out[1..], 1);
                }

                3 => {
                    out[0] = 250;
                    return self.do_encode(&mut out[1..], 1);
                }

                4 => {
                    out[0] = 251;
                    return self.do_encode(&mut out[1..], 1);
                }

                5 => {
                    out[0] = 252;
                    return self.do_encode(&mut out[1..], 1);
                }

                6 => {
                    out[0] = 253;
                    return self.do_encode(&mut out[1..], 1);
                }

                7 => {
                    out[0] = 254;
                    return self.do_encode(&mut out[1..], 1);
                }

                8 => {
                    out[0] = 255;
                    return self.do_encode(&mut out[1..], 1);
                }

                _ => unreachable!(), // encoding_length() - 1 is always between 0 and 8 (inclusive)
            }
        } else {
            self.remaining -= 1;
            out[0] = (self.n >> (8 * self.remaining)) as u8;
            self.n >>= 8;

            if self.remaining == 0 {
                return total_output + 1;
            } else {
                return self.do_encode(&mut out[1..], total_output + 1);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;

    fn decode_all(data: &[u8],
                  dec: &mut super::Decoder,
                  chunk_size: usize)
                  -> (usize, Result<u64, Option<super::DecodeError>>) {
        let mut consumed = 0;

        for chunk in data.chunks(chunk_size) {
            match dec.decode(chunk) {
                (eaten, None) => consumed += eaten,
                (eaten, Some(Ok(decoded))) => {
                    return (consumed + eaten, Ok(decoded));
                }
                (eaten, Some(Err(e))) => return (consumed + eaten, Err(Some(e))),
            }
        }

        return (consumed, Err(None));
    }

    quickcheck! {
          fn test_decoder(data: Vec<u8>, chunk_size: u8) -> bool {
              let mut dec = super::Decoder::new();

              match decode(&data) {
                  Err((DecodeError::UnexpectedEndOfInput, tail)) => {
                      let (consumed, tmp) = decode_all(&data, &mut dec, chunk_size as usize);
                      assert!(tmp.unwrap_err().is_none());
                      assert_eq!(consumed, data.len() - tail.len());
                  }

                  Err((err, tail)) => {
                      let (consumed, tmp) = decode_all(&data, &mut dec, chunk_size as usize);
                      let nb_err = tmp.unwrap_err().unwrap();
                      assert_eq!(consumed, data.len() - tail.len());
                  }

                  Ok((decoded, tail)) => {
                      let (consumed, tmp) = decode_all(&data, &mut dec, (chunk_size as usize) + 1);
                      let nb_decoded = tmp.unwrap();
                      assert_eq!(nb_decoded, decoded);
                      assert_eq!(consumed, data.len() -tail.len())
                  }
              }

              true
          }
      }

    fn encode_all<'a, I: Iterator<Item = &'a mut [u8]>>(enc: &mut super::Encoder,
                                                        outs: &mut I)
                                                        -> usize {
        let mut total_written = 0;

        for out in outs {
            let written = enc.encode(out);
            total_written += written;

            if written == 0 && out.len() > 0 {
                return total_written;
            }
        }

        if enc.encode(&mut [42]) == 0 {
            return total_written;
        } else {
            panic!();
        }
    }

    quickcheck! {
        fn test_encoder(n: u64, chunk_size: u8) -> bool {
            let mut enc = super::Encoder::new(n);

            let mut buf = vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
            let mut nb_buf = vec![0, 0, 0, 0, 0, 0, 0, 0, 0];

            let written = encode(n, &mut buf);
            let nb_written = encode_all(&mut enc, &mut nb_buf.chunks_mut((chunk_size as usize) + 1));

            assert_eq!(nb_written, written);
            assert_eq!(&nb_buf[..nb_written], &buf[..written]);

            true
        }
    }
}
