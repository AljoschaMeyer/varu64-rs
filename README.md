# VarU64

An encoding of unsigned 64 bit integers, using continuation bits to save space for low numbers. This is the same as the [multiformats varint](https://github.com/multiformats/unsigned-varint/blob/8a6574bd229d9e158dad43acbcea7763b7807362/README.md), except that on nine-byte varints, the most significant bit is not a continuation bit. So 2^64 - 1 can be encoded as nine bytes of `11111111` each.
