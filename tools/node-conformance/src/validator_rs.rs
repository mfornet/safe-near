//! Reed-Solomon fixtures.

use crate::{hex, Out};
use near_primitives::reed_solomon::{
    reed_solomon_decode, reed_solomon_encode, reed_solomon_num_data_parts, reed_solomon_part_length,
};
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use reed_solomon_erasure::galois_8::{self, ReedSolomon};
use serde_json::json;

fn rng(label: &str) -> ChaCha8Rng {
    let mut seed = 0x5eed_u64;
    for b in label.bytes() {
        seed = (seed ^ b as u64).wrapping_mul(0x100000001b3);
    }
    ChaCha8Rng::seed_from_u64(seed)
}

fn shards_json(s: &[Option<Vec<u8>>]) -> serde_json::Value {
    s.iter().map(|x| x.as_ref().map(|b| hex(b))).collect::<Vec<_>>().into()
}

const CONFIGS: &[(usize, usize)] = &[
    (1, 1), (2, 1), (1, 2), (2, 2), (3, 2), (4, 3), (5, 3), (6, 4), (10, 4), (17, 6), (30, 20), (100, 55),
    (171, 84), (200, 55), (255, 1), (1, 255),
];

pub fn reed_solomon(out: &mut Out) {
    // The field.
    let mut mul = vec![];
    for a in 0..=255u8 {
        for b in 0..=255u8 {
            mul.push(galois_8::mul(a, b));
        }
    }
    let mut div = vec![];
    for a in 0..=255u8 {
        for b in 1..=255u8 {
            div.push(galois_8::div(a, b));
        }
    }
    let mut exp = vec![];
    for a in 0..=255u8 {
        for n in 0..=300usize {
            exp.push(galois_8::exp(a, n));
        }
    }
    out.line("gf", json!({"mul": hex(&mul), "div": hex(&div), "exp": hex(&exp), "expMax": 300}));

    // The number of data parts and the part length.
    for total in 0..=255usize {
        for (ratio, name) in [(0.6, "0.6")] {
            out.line("rs-parts", json!({
                "total": total, "ratio": name,
                "dataParts": reed_solomon_num_data_parts(total, ratio),
            }));
        }
    }
    for len in [0usize, 1, 2, 3, 10, 100, 1000, 1_000_003] {
        for k in [1usize, 2, 3, 7, 60] {
            out.line("rs-part-length", json!({
                "length": len, "dataParts": k, "partLength": reed_solomon_part_length(len, k),
            }));
        }
    }

    // The code: parity of random data shards.
    let mut g = rng("rs-encode");
    for &(d, p) in CONFIGS {
        for len in [1usize, 2, 5, 33] {
            let rs = ReedSolomon::new(d, p).unwrap();
            let mut shards: Vec<Vec<u8>> = (0..d)
                .map(|_| {
                    let mut v = vec![0u8; len];
                    g.fill_bytes(&mut v);
                    v
                })
                .collect();
            shards.extend((0..p).map(|_| vec![0u8; len]));
            rs.encode(&mut shards).unwrap();
            let data: Vec<_> = shards[..d].iter().map(|b| hex(b)).collect();
            let parity: Vec<_> = shards[d..].iter().map(|b| hex(b)).collect();
            out.line("rs-encode", json!({"data": d, "parity": p, "dataShards": data, "parityShards": parity}));
        }
    }
    // Invalid construction and inputs.
    for (d, p) in [(0usize, 1usize), (1, 0), (200, 100), (256, 1)] {
        out.line("rs-new", json!({"data": d, "parity": p, "error": ReedSolomon::new(d, p).err().map(|e| format!("{e:?}"))}));
    }
    for (d, p) in [(2usize, 1usize), (1, 1)] {
        let rs = ReedSolomon::new(d, p).unwrap();
        let mut empty: Vec<Vec<u8>> = vec![vec![]; d + p];
        let e1 = rs.encode(&mut empty).err().map(|e| format!("{e:?}"));
        out.line("rs-encode-error", json!({"data": d, "parity": p, "case": "empty", "error": e1}));
        if d >= 2 {
            let mut uneven: Vec<Vec<u8>> = vec![vec![1, 2], vec![3], vec![0, 0]];
            let e2 = rs.encode(&mut uneven).err().map(|e| format!("{e:?}"));
            out.line("rs-encode-error", json!({"data": d, "parity": p, "case": "uneven", "error": e2}));
        }
    }

    // Reconstruction from every kind of erasure pattern.
    let mut g = rng("rs-reconstruct");
    for &(d, p) in CONFIGS {
        let rs = ReedSolomon::new(d, p).unwrap();
        let total = d + p;
        for case in 0..14 {
            let len = 1 + (g.next_u32() % 40) as usize;
            let mut shards: Vec<Vec<u8>> = (0..d)
                .map(|_| {
                    let mut v = vec![0u8; len];
                    g.fill_bytes(&mut v);
                    v
                })
                .collect();
            shards.extend((0..p).map(|_| vec![0u8; len]));
            rs.encode(&mut shards).unwrap();
            // which shards stay present
            let mut keep = vec![true; total];
            let missing = match case {
                0 => 0,
                1 => 1.min(p),
                2 => p,
                3 => p + 1,
                4 => total,
                _ => (g.next_u32() as usize) % (p + 2),
            }
            .min(total);
            let mut order: Vec<usize> = (0..total).collect();
            for i in (1..total).rev() {
                order.swap(i, (g.next_u32() as usize) % (i + 1));
            }
            if case == 5 {
                // all data shards missing as far as the parity allows
                order = (0..d).chain(d..total).collect();
            }
            for &i in order.iter().take(missing) {
                keep[i] = false;
            }
            let mut opt: Vec<Option<Vec<u8>>> =
                shards.iter().enumerate().map(|(i, s)| keep[i].then(|| s.clone())).collect();
            let input = shards_json(&opt);
            let result = rs.reconstruct(&mut opt);
            match result {
                Ok(()) => {
                    let full: Vec<_> = opt.iter().map(|s| hex(s.as_ref().unwrap())).collect();
                    assert!(opt.iter().zip(&shards).all(|(a, b)| a.as_ref().unwrap() == b));
                    out.line("rs-reconstruct", json!({"data": d, "parity": p, "shards": input, "result": full}));
                }
                Err(e) => {
                    out.line("rs-reconstruct", json!({"data": d, "parity": p, "shards": input, "error": format!("{e:?}")}));
                }
            }
        }
    }
    // Errors of reconstruction with bad inputs.
    let rs = ReedSolomon::new(2, 1).unwrap();
    for (name, mut s) in [
        ("uneven", vec![Some(vec![1u8, 2]), Some(vec![3]), None]),
        ("empty-present", vec![Some(vec![]), Some(vec![]), None]),
        ("all-empty", vec![Some(vec![]), Some(vec![]), Some(vec![])]),
        ("wrong-count", vec![Some(vec![1u8]), None]),
    ] {
        let input = shards_json(&s);
        let r = rs.reconstruct(&mut s);
        out.line("rs-reconstruct", json!({"data": 2, "parity": 1, "shards": input, "error": r.err().map(|e| format!("{e:?}")), "name": name}));
    }

    // The wrapper of near-primitives: encode and decode a `Vec<u8>` (its Borsh encoding is a length
    // prefix and the bytes).
    let mut g = rng("rs-bytes");
    for &(d, p) in CONFIGS.iter().filter(|c| c.0 + c.1 < 120) {
        let rs = ReedSolomon::new(d, p).unwrap();
        for payload in [0usize, 1, 3, 17, 255, 4096, 10_000] {
            let mut data = vec![0u8; payload];
            g.fill_bytes(&mut data);
            let borsh = borsh::to_vec(&data).unwrap();
            let (parts, encoded_length) = reed_solomon_encode(&rs, &data);
            let all: Vec<_> = parts.iter().map(|x| hex(x.as_ref().unwrap())).collect();
            out.line("rs-bytes", json!({
                "data": d, "parity": p, "borsh": hex(&borsh), "parts": all, "encodedLength": encoded_length,
            }));
            // decode with erasures (the small cases only: the files are committed)
            if !(payload <= 255 && d + p <= 30 || (d, p, payload) == (4, 3, 4096)) {
                continue;
            }
            for erase in [0usize, 1, p, p + 1] {
                let mut opt: Vec<Option<Box<[u8]>>> = parts.clone();
                let mut order: Vec<usize> = (0..d + p).collect();
                for i in (1..order.len()).rev() {
                    order.swap(i, (g.next_u32() as usize) % (i + 1));
                }
                for &i in order.iter().take(erase.min(d + p)) {
                    opt[i] = None;
                }
                let input: Vec<_> = opt.iter().map(|x| x.as_ref().map(|b| hex(b))).collect();
                for len_delta in [0i64, -1, 1] {
                    let length = (encoded_length as i64 + len_delta).max(0) as usize;
                    let mut copy = opt.clone();
                    let r = reed_solomon_decode::<Vec<u8>>(&rs, &mut copy, length);
                    let line = match r {
                        Ok(v) => json!({"data": d, "parity": p, "parts": input, "encodedLength": length, "ok": hex(&borsh::to_vec(&v).unwrap())}),
                        Err(e) => json!({"data": d, "parity": p, "parts": input, "encodedLength": length, "error": e.to_string()}),
                    };
                    out.line("rs-decode", line);
                }
            }
        }
    }
}
