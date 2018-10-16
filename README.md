# VarU64

An encoding of unsigned 64 bit integers: Numbers up below 248 are encoded in a single byte, other numbers are encoded with as few bytes as possible (big-endian), proceded by a tag indicating how many bytes the number contains in total.
