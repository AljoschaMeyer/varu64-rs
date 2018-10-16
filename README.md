# VarU64

A simple variable-length encoding for unsigned 64 bit integers.

## Specification

To decode a varu64, look at the first byte. If its value is below 248, the value itself is the encoded number. Else, the first byte determines the further `length` of the encoding:

| first byte | number of additional bytes |
|------------|----------------------------|
| 248 | 1 |
| 249 | 2 |
| 250 | 3 |
| 251 | 4 |
| 252 | 5 |
| 253 | 6 |
| 254 | 7 |
| 255 | 8 |

Following the first byte are `length` many bytes. These bytes are the big-endian representation of the encoded number.

Of all possible representation for a number that this scheme admits, the shortest one is its unique, valid encoding. Decoders must indicate an error if a value uses an encoding that is longer than necessary.

## Remarks/Properties

Whether the first byte signifies a length can be efficiently checked by testing whether the first 5 bits are set to 1. In that case, the length itself is 1 plus the value of the last three bits.

The length of an encoded value can be determined by solely looking at the first byte.

Due to the canonicity requirement of only allowing the shortest possible encoding, there is a bijection between unsigned 64 bit integers and encodings.

The cost for the simplicity and canonicty of this format are a (somewhat) large number of unused byte strings. On the plus side, these can be used as extension points.

Related work: This has been inspired by the issues in the [multiformats varint](TODO) repository, in particular issues [#TODO](TODO) and [#TODO](TODO).
