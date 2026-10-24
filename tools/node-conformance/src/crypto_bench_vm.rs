//! Native timings of the pairing-friendly curves and P-256 host functions: `near-vm-runner`'s own
//! `VMLogic` (so the cost of decoding and checking the points is included, as in the node) on
//! inputs taken from the committed fixtures, which are valid and of the sizes named.

use crate::crypto_vm::Vm;
use crate::{measure, report};
use serde_json::Value;
use std::hint::black_box;

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

/// The `field` of the fixture line `kind`/`name` in `file`, as bytes.
fn fixture(file: &str, kind: &str, name: &str, field: &str) -> Vec<u8> {
    let path = format!("{}/../../near-lean/crypto/fixtures/{file}", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).unwrap();
    for line in text.lines() {
        let v: Value = serde_json::from_str(line).unwrap();
        if v["kind"] == kind && v["name"] == name {
            return unhex(v[field].as_str().unwrap());
        }
    }
    panic!("no line {kind}/{name} in {file}");
}

pub fn curves() {
    let vm = Vm::with_memory(true, 1 << 17);
    // BN254: a pairing check of two pairs, eight points
    let mut pairing = fixture("bn254.jsonl", "pairing_check", "scalar-move-true-0", "input");
    assert_eq!(pairing.len(), 384);
    let mut pairing1 = fixture("bn254.jsonl", "pairing_check", "random-single-0", "input");
    let mut multiexp = fixture("bn254.jsonl", "g1_multiexp", "random-8", "input");
    let mut multiexp1 = fixture("bn254.jsonl", "g1_multiexp", "random-1", "input");
    let mut sum = fixture("bn254.jsonl", "g1_sum", "random-8", "input");
    // the first byte of the input changes with the iteration where that keeps it valid: the sign
    // of a sum, otherwise the scalar; the pairing inputs swap their two pairs
    report("bn254/pairing-1", measure(|i| {
        pairing1[0] ^= 0;
        vm.bn_pairing(black_box(&pairing1)).map_or(2, |b| b as u64) + i as u64 % 1
    }));
    report("bn254/pairing-2", measure(|i| {
        if i % 2 == 1 {
            pairing.rotate_left(192);
        }
        vm.bn_pairing(black_box(&pairing)).map_or(2, |b| b as u64)
    }));
    report("bn254/g1-multiexp-1", measure(|i| {
        multiexp1[64] = (i % 7) as u8;
        vm.bn_g1(true, black_box(&multiexp1)).unwrap()[0] as u64
    }));
    report("bn254/g1-multiexp-8", measure(|i| {
        multiexp[64] = (i % 7) as u8;
        vm.bn_g1(true, black_box(&multiexp)).unwrap()[0] as u64
    }));
    report("bn254/g1-sum-8", measure(|i| {
        sum[0] = (i % 2) as u8;
        vm.bn_g1(false, black_box(&sum)).unwrap()[0] as u64
    }));

    // BLS12-381 (the host functions of protocol 86: the fix is off, which changes nothing here)
    let vm = Vm::with_memory(false, 1 << 17);
    let mut pairing = fixture("bls12381.jsonl", "pairing_check", "scalar-move-true-0", "input");
    assert_eq!(pairing.len(), 576);
    let mut pairing1 = fixture("bls12381.jsonl", "pairing_check", "random-single-0", "input");
    let mut p1_sum = fixture("bls12381.jsonl", "p1_sum", "random-8", "input");
    let mut p2_sum = fixture("bls12381.jsonl", "p2_sum", "random-8", "input");
    let mut g1_mul = fixture("bls12381.jsonl", "g1_multiexp", "random-8", "input");
    let mut g2_mul = fixture("bls12381.jsonl", "g2_multiexp", "random-8", "input");
    let mut g1_mul1 = fixture("bls12381.jsonl", "g1_multiexp", "random-1", "input");
    let mut g2_mul1 = fixture("bls12381.jsonl", "g2_multiexp", "random-1", "input");
    let mut map1 = fixture("bls12381.jsonl", "map_fp_to_g1", "random-0", "input");
    let mut map2 = fixture("bls12381.jsonl", "map_fp2_to_g2", "random-0", "input");
    let mut dec1 = fixture("bls12381.jsonl", "p1_decompress", "random", "input");
    let mut dec2 = fixture("bls12381.jsonl", "p2_decompress", "random", "input");
    let ret = |r: Option<crate::crypto_vm::Reply>| r.map_or(2, |r| r.ret + r.out.first().copied().unwrap_or(0) as u64);
    report("bls12381/pairing-1", measure(|i| {
        pairing1[0] ^= 0;
        ret(vm.bls("pairing_check", black_box(&pairing1))) + i as u64 % 1
    }));
    report("bls12381/pairing-2", measure(|i| {
        if i % 2 == 1 {
            pairing.rotate_left(288);
        }
        ret(vm.bls("pairing_check", black_box(&pairing)))
    }));
    report("bls12381/p1-sum-8", measure(|i| {
        p1_sum[0] = (i % 2) as u8;
        ret(vm.bls("p1_sum", black_box(&p1_sum)))
    }));
    report("bls12381/p2-sum-8", measure(|i| {
        p2_sum[0] = (i % 2) as u8;
        ret(vm.bls("p2_sum", black_box(&p2_sum)))
    }));
    report("bls12381/g1-multiexp-1", measure(|i| {
        g1_mul1[96] = (i % 7) as u8;
        ret(vm.bls("g1_multiexp", black_box(&g1_mul1)))
    }));
    report("bls12381/g1-multiexp-8", measure(|i| {
        g1_mul[96] = (i % 7) as u8;
        ret(vm.bls("g1_multiexp", black_box(&g1_mul)))
    }));
    report("bls12381/g2-multiexp-1", measure(|i| {
        g2_mul1[192] = (i % 7) as u8;
        ret(vm.bls("g2_multiexp", black_box(&g2_mul1)))
    }));
    report("bls12381/g2-multiexp-8", measure(|i| {
        g2_mul[192] = (i % 7) as u8;
        ret(vm.bls("g2_multiexp", black_box(&g2_mul)))
    }));
    report("bls12381/map-fp-to-g1", measure(|i| {
        map1[47] = i as u8;
        ret(vm.bls("map_fp_to_g1", black_box(&map1)))
    }));
    report("bls12381/map-fp2-to-g2", measure(|i| {
        map2[95] = i as u8;
        ret(vm.bls("map_fp2_to_g2", black_box(&map2)))
    }));
    report("bls12381/p1-decompress", measure(|i| {
        dec1[0] = 0x80 | (i % 2) as u8 * 0x20 | (dec1[0] & 0x1f);
        ret(vm.bls("p1_decompress", black_box(&dec1)))
    }));
    report("bls12381/p2-decompress", measure(|i| {
        dec2[0] = 0x80 | (i % 2) as u8 * 0x20 | (dec2[0] & 0x1f);
        ret(vm.bls("p2_decompress", black_box(&dec2)))
    }));

    // P-256: a valid signature over a 32-byte digest
    let sig = fixture("p256.jsonl", "verify", "valid-len-32", "sig");
    let mut msg = fixture("p256.jsonl", "verify", "valid-len-32", "msg");
    let pk = fixture("p256.jsonl", "verify", "valid-len-32", "pk");
    report("p256/verify-32B", measure(|i| {
        msg[31] = msg[31].wrapping_add(i as u8 & 1);
        vm.p256(&sig, black_box(&msg), &pk).unwrap_or(2)
    }));
}
