//! Native timings of the primitives that `near-lean/crypto` implements, with the crates
//! nearcore uses, in release mode: `cargo run --release --locked --bin crypto-bench`. Prints one
//! JSON object per line: `{"name", "nanosPerIteration"}`. The names match `node-bench`.

use near_crypto::{ED25519PublicKey, ED25519SecretKey, KeyType, PublicKey, SecretKey, Signature};
use near_primitives::hash::CryptoHash;
use ripemd::Ripemd160;
use sha2::{Digest, Sha512};
use sha3::{Keccak256, Keccak512};
use std::hint::black_box;
use std::time::Instant;

fn input(n: usize, seed: usize) -> Vec<u8> {
    (0..n).map(|i| (i * 31 + seed) as u8).collect()
}

/// Mean nanoseconds per call of `f`, after a warm-up, over at least 0.3 s.
fn measure(mut f: impl FnMut(usize) -> u64) -> u64 {
    let mut acc = 0u64;
    for i in 0..20 {
        acc ^= f(i);
    }
    let mut iterations = 0u64;
    let start = Instant::now();
    while start.elapsed().as_millis() < 300 {
        for i in 0..10 {
            acc ^= f(i);
        }
        iterations += 10;
    }
    black_box(acc);
    start.elapsed().as_nanos() as u64 / iterations
}

fn report(name: &str, nanos: u64) {
    println!("{{\"name\":\"{name}\",\"nanosPerIteration\":{nanos}}}");
}

fn main() {
    for (label, size) in [("64B", 64usize), ("1KiB", 1024), ("64KiB", 65536)] {
        let mut data = input(size, 3);
        report(&format!("sha256/{label}"), measure(|i| {
            data[0] = i as u8;
            CryptoHash::hash_bytes(black_box(&data)).0[0] as u64
        }));
        report(&format!("sha512/{label}"), measure(|i| {
            data[0] = i as u8;
            Sha512::digest(black_box(&data))[0] as u64
        }));
        report(&format!("keccak256/{label}"), measure(|i| {
            data[0] = i as u8;
            Keccak256::digest(black_box(&data))[0] as u64
        }));
        report(&format!("keccak512/{label}"), measure(|i| {
            data[0] = i as u8;
            Keccak512::digest(black_box(&data))[0] as u64
        }));
        report(&format!("ripemd160/{label}"), measure(|i| {
            data[0] = i as u8;
            Ripemd160::digest(black_box(&data))[0] as u64
        }));
    }
    let seed = [7u8; 32];
    let keypair = ed25519_dalek::SigningKey::from_bytes(&seed).to_keypair_bytes();
    let secret = SecretKey::ED25519(ED25519SecretKey(keypair));
    let public = PublicKey::ED25519(ED25519PublicKey(keypair[32..].try_into().unwrap()));
    let mut message = input(100, 5);
    let signature = secret.sign(&message);
    // `Signature::verify` as nearcore calls it: decode the key, then the non-strict check.
    report("ed25519/verify", measure(|i| {
        message[0] = i as u8;
        signature.verify(black_box(&message), black_box(&public)) as u64
    }));
    // `SecretKey::sign` decodes the key pair (one derivation) before every signature.
    report("ed25519/sign", measure(|i| {
        message[0] = i as u8;
        match secret.sign(black_box(&message)) {
            Signature::ED25519(s) => s.to_bytes()[0] as u64,
            _ => 0,
        }
    }));
    // The prepared key: the expanded secret is held, so only the signing arithmetic remains.
    let prepared = ed25519_dalek::SigningKey::from_bytes(&seed);
    report("ed25519/sign-prepared", measure(|i| {
        message[0] = i as u8;
        ed25519_dalek::Signer::sign(&prepared, black_box(&message)).to_bytes()[0] as u64
    }));
    let _ = KeyType::ED25519;
}
