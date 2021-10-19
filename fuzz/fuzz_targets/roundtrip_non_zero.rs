#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate varu64;

use varu64::{encode_non_zero_u64, decode_non_zero_u64};

fuzz_target!(|data: &[u8]| {
    // test that roundtrips work
    match decode_non_zero_u64(data) {
        Err(_) => {}
        Ok((n, tail)) => {
            let len = data.len() - tail.len();
            let mut enc = [0u8; 9];
            assert_eq!(encode_non_zero_u64(n, &mut enc[..]), len);
            assert_eq!(&enc[..len], &data[..len]);
        }
    }
});
