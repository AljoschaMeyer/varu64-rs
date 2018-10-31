#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate varu64;

use varu64::{encode, decode};

fuzz_target!(|data: &[u8]| {
    // test that roundtrips work
    match decode(data) {
        Err(_) => {}
        Ok((n, tail)) => {
            let len = data.len() - tail.len();
            let mut enc = [0u8; 9];
            assert_eq!(encode(n, &mut enc[..]), len);
            assert_eq!(&enc[..len], &data[..len]);
        }
    }
});
