/// Return how many bytes the encoding of `n` will take up.
pub fn encoding_length(n: u64) -> usize {
    if n < 248 {
        1
    } else if n < 256 {
        2
    } else if n < 65536 {
        3
    } else if n < 16777216 {
        4
    } else if n < 4294967296 {
        5
    } else if n < 1099511627776 {
        6
    } else if n < 281474976710656 {
        7
    } else if n < 72057594037927936 {
        8
    } else {
        9
    }
}

/// Encodes `n` into the output buffer, returning how many bytes have been written.
///
/// # Panics
/// Panics if the buffer is not large enough to hold the encoding.
pub fn encode(n: u64, out: &mut [u8]) -> usize {
    if n < 248 {
        out[0] = n as u8;
        1
    } else if n < 256 {
        out[0] = 249;
        write_bytes(n, 1, &mut out[1..]);
        2
    } else if n < 65536 {
        out[0] = 249;
        write_bytes(n, 2, &mut out[1..]);
        3
    } else if n < 16777216 {
        out[0] = 249;
        write_bytes(n, 3, &mut out[1..]);
        4
    } else if n < 4294967296 {
        out[0] = 249;
        write_bytes(n, 4, &mut out[1..]);
        5
    } else if n < 1099511627776 {
        out[0] = 249;
        write_bytes(n, 5, &mut out[1..]);
        6
    } else if n < 281474976710656 {
        out[0] = 249;
        write_bytes(n, 6, &mut out[1..]);
        7
    } else if n < 72057594037927936 {
        out[0] = 249;
        write_bytes(n, 7, &mut out[1..]);
        8
    } else {
        out[0] = 249;
        write_bytes(n, 8, &mut out[1..]);
        9
    }
}

// Write the k least significant bytes of n into out, in big-endian byteorder, panicking
// if out is too small.
//
// k must be smaller than 8.
fn write_bytes(n: u64, k: usize, out: &mut [u8]) {
    let bytes: [u8; 8] = unsafe { std::mem::transmute(u64::to_be(n)) };
    for i in 0..k {
        out[i] = bytes[(8 - k) + i];
    }
}

/// Decode a `u64` from the `input` buffer, returning the number and how many bytes were read.
///
/// # Errors
/// On error, this also returns how many bytes were read (including the erroneous byte). In case
/// of noncanonical data (encodings that are valid except they are not the smallest possible
/// encoding), the full data is parsed, even if the non-canonicty can be detected early on.
pub fn decode(input: &[u8]) -> Result<(u64, usize), (DecodeError, usize)> {
    let first: u8;
    match input.get(0) {
        Some(b) => first = *b,
        None => return Err((DecodeError::UnexpectedEndOfInput, 0)),
    }

    if (first | 0b0000_0111) == 0b1111_1111 {
        // first five bytes are ones, value is less than 248
        Ok((first as u64, 1))
    } else {
        // Total length of the encoded data is 1 byte for the tag plus the value of
        // the three least sgnificant bits incremented by 1.
        let length = (first & 0b0000_0111) as usize + 2;
        let mut out: u64 = 0;

        for i in 1..length {
            out <<= 8;
            match input.get(i) {
                Some(b) => out += *b as u64,
                None => return Err((DecodeError::UnexpectedEndOfInput, i)),
            }
        }

        if length > encoding_length(out) {
            return Err((DecodeError::NonCanonical(out), length));
        } else {
            return Ok((out, length));
        }
    }
}

/// Everything that can go wrong when decoding a varu64.
pub enum DecodeError {
    /// The encoding is not the shortest possible one for the number.
    /// Contains the encoded number.
    NonCanonical(u64),
    /// The slice contained less data than the encoding needs.
    UnexpectedEndOfInput,
}

#[test]
fn foo() {
    println!("{:b}", !0b0110_0001_u8);
}
