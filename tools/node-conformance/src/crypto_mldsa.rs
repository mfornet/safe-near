//! SHAKE and ML-DSA-65 fixtures (`shake.jsonl`, `mldsa.jsonl`).
//!
//! * SHAKE128 and SHAKE256 come from `sha3` 0.10.9, the crate nearcore's dependencies use for the
//!   Keccak family.
//! * ML-DSA-65 is `near-crypto` 0.37.4's `MLDSA65` key type, which delegates to `aws-lc-rs` 1.16.2
//!   (`aws-lc-sys` 0.39.1, AWS-LC's `mldsa-native` based ML-DSA, FIPS 204 final):
//!   - keys: `PqdsaKeyPair::from_seed(&ML_DSA_65_SIGNING, seed)` with the 32-byte FIPS 204 seed
//!     `ξ`, exported as the 4032-byte raw private key (`ml_dsa_65_secret_from_seed`, a private
//!     function of `near-crypto`, so the oracle repeats its two calls), and
//!     `PqdsaKeyPair::from_raw_private_key` for a key given as bytes (`SecretKey::from_str` and
//!     `SecretKey::sign` call it; it also rederives the public key and rejects a key whose `s1`, `s2`,
//!     `t0` or `tr` are inconsistent);
//!   - `SecretKey::sign` is `PqdsaKeyPair::sign` (`EVP_DigestSign`: pure ML-DSA, empty context,
//!     hedged with 32 fresh random bytes), so a signature is never reproducible. The oracle calls
//!     the same C function with the random bytes chosen (`ml_dsa_65_sign_internal(sk, msg, pre =
//!     0x00 0x00, rnd)`, the body of `ml_dsa_65_sign` after it draws `rnd`), checks with
//!     `near-crypto` that the result verifies, and records `rnd`;
//!   - `Signature::verify` is `UnparsedPublicKey::new(&ML_DSA_65, pk).verify(msg, sig)`
//!     (`ml_dsa_65_verify` with an empty context). The verdicts below are from `near-crypto` where
//!     its fixed-size types can hold the input and from `aws-lc-rs` directly otherwise.

use super::{hex, Out, Rng};
use aws_lc_rs::encoding::{AsRawBytes, PqdsaPrivateKeyRaw};
use aws_lc_rs::signature::{KeyPair, UnparsedPublicKey};
use aws_lc_rs::unstable::signature::{PqdsaKeyPair, ML_DSA_65, ML_DSA_65_SIGNING};
use near_crypto::{KeyType, MlDsa65PublicKey, PublicKey, SecretKey, Signature};
use serde_json::json;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Digest, Sha3_256, Shake128, Shake256};

const PK_LEN: usize = 1952;
const SK_LEN: usize = 4032;
const SIG_LEN: usize = 3309;
const C_TILDE: usize = 48;
const Z_END: usize = C_TILDE + 5 * 640;
const OMEGA: usize = 55;
const GAMMA1: u32 = 1 << 19;
const BETA: u32 = 196;

unsafe extern "C" {
    /// `ml_dsa_65_sign_internal` of AWS-LC (the symbol is prefixed with the `aws-lc-sys` version).
    #[link_name = "aws_lc_0_39_1_ml_dsa_65_sign_internal"]
    fn ml_dsa_65_sign_internal(
        sk: *const u8,
        sig: *mut u8,
        sig_len: *mut usize,
        msg: *const u8,
        msg_len: usize,
        pre: *const u8,
        pre_len: usize,
        rnd: *const u8,
    ) -> i32;
    /// The same with `mu` (64 bytes) in place of the message (`ExternalMu`).
    #[link_name = "aws_lc_0_39_1_ml_dsa_extmu_65_sign_internal"]
    fn ml_dsa_extmu_65_sign_internal(
        sk: *const u8,
        sig: *mut u8,
        sig_len: *mut usize,
        mu: *const u8,
        mu_len: usize,
        pre: *const u8,
        pre_len: usize,
        rnd: *const u8,
    ) -> i32;
}

// ---------------------------------------------------------------------------------------------
// SHAKE

fn shake(alg: &str, msg: &[u8], n: usize) -> Vec<u8> {
    let mut out = vec![0u8; n];
    match alg {
        "shake128" => {
            let mut h = Shake128::default();
            h.update(msg);
            h.finalize_xof().read(&mut out);
        }
        "shake256" => {
            let mut h = Shake256::default();
            h.update(msg);
            h.finalize_xof().read(&mut out);
        }
        _ => unreachable!(),
    }
    out
}

pub fn shake_fixtures(out: &mut Out) {
    assert_eq!(hex(&shake("shake128", b"", 32)), "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26");
    assert_eq!(hex(&shake("shake256", b"", 32)), "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f");
    assert_eq!(hex(&shake("shake128", b"abc", 16)), "5881092dd818bf5cf8a3ddb793fbcba7");
    assert_eq!(hex(&shake("shake256", b"abc", 32)), "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739");
    for (alg, rate) in [("shake128", 168usize), ("shake256", 136)] {
        let mut rng = Rng::new(super::fnv(alg));
        // Message lengths around the rate: the padding byte alone, the block full, one over.
        let mut lengths = vec![0usize, 1, 2, 3, 31, 32, 33, 64, 100, 200, 500, 1000, 4096];
        for m in 1..=3 {
            for d in [-2i64, -1, 0, 1, 2] {
                lengths.push((m * rate as i64 + d) as usize);
            }
        }
        lengths.push(rate - 3);
        lengths.sort();
        lengths.dedup();
        // Output lengths: one byte, a hash, around one and several blocks, a long stream.
        let outs = [1usize, 16, 32, 64, rate - 1, rate, rate + 1, 2 * rate, 3 * rate + 5, 1000, 5000];
        for (i, n) in lengths.iter().enumerate() {
            let msg = rng.bytes(*n);
            for k in 0..3 {
                let len = outs[(i * 3 + k * 4 + k) % outs.len()];
                out.push("shake", json!({"kind": "shake", "alg": alg, "name": format!("msg-{n}-out-{len}"), "msg": hex(&msg), "outLen": len, "digest": hex(&shake(alg, &msg, len))}));
            }
        }
        // Every output length around the first blocks for one message.
        let msg = rng.bytes(77);
        for len in 1..=3 * rate + 2 {
            if len > 4 && len % 7 != 0 && len + 3 < 3 * rate && (len < rate - 2 || len > rate + 2) && (len < 2 * rate - 2 || len > 2 * rate + 2) {
                continue;
            }
            out.push("shake", json!({"kind": "shake", "alg": alg, "name": format!("stream-{len}"), "msg": hex(&msg), "outLen": len, "digest": hex(&shake(alg, &msg, len))}));
        }
        let million = vec![b'a'; 1_000_000];
        out.push("shake", json!({"kind": "shake", "alg": alg, "name": "million-a", "unit": "61", "count": 1_000_000, "outLen": 64, "digest": hex(&shake(alg, &million, 64))}));
    }

    // SHA3-256 (the padding 0x06, rate 136): `near-crypto` hashes an ML-DSA-65 public key with it.
    assert_eq!(hex(&Sha3_256::digest(b"")), "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a");
    assert_eq!(hex(&Sha3_256::digest(b"abc")), "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532");
    let mut rng = Rng::new(super::fnv("sha3_256"));
    for n in [0usize, 1, 2, 3, 31, 32, 33, 64, 100, 134, 135, 136, 137, 200, 271, 272, 273, 500, 1000, 1952, 1981, 4096] {
        let msg = rng.bytes(n);
        out.push("shake", json!({"kind": "shake", "alg": "sha3_256", "name": format!("msg-{n}-out-32"), "msg": hex(&msg), "outLen": 32, "digest": hex(&Sha3_256::digest(&msg))}));
    }
    let million = vec![b'a'; 1_000_000];
    out.push("shake", json!({"kind": "shake", "alg": "sha3_256", "name": "million-a", "unit": "61", "count": 1_000_000, "outLen": 32, "digest": hex(&Sha3_256::digest(&million))}));
}

// ---------------------------------------------------------------------------------------------
// ML-DSA-65

struct Key {
    name: String,
    pk: Vec<u8>,
    sk: Vec<u8>,
}

fn raw_private(kp: &PqdsaKeyPair) -> Vec<u8> {
    let raw: PqdsaPrivateKeyRaw<'static> = kp.private_key().as_raw_bytes().expect("raw export");
    let bytes: &[u8] = raw.as_ref();
    bytes.to_vec()
}

/// `near-crypto`'s `ml_dsa_65_from_seed` (two `aws-lc-rs` calls), then the parse and the public key
/// as `SecretKey::from_str` and `SecretKey::public_key` do it.
fn keygen(name: &str, seed: [u8; 32]) -> Key {
    let kp = PqdsaKeyPair::from_seed(&ML_DSA_65_SIGNING, &seed).unwrap();
    let sk = raw_private(&kp);
    let pk: &[u8] = kp.public_key().as_ref();
    assert_eq!((pk.len(), sk.len()), (PK_LEN, SK_LEN));
    let parsed: SecretKey = format!("ml-dsa-65:{}", bs58::encode(&sk).into_string()).parse().unwrap();
    assert_eq!(parsed.public_key().key_data(), pk);
    Key { name: name.to_string(), pk: pk.to_vec(), sk }
}

/// The verdict of `Signature::verify` (`near-crypto`) when its types can hold the input, and of
/// `aws-lc-rs` otherwise; both are asserted equal where both apply.
fn verdict(pk: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    let direct = UnparsedPublicKey::new(&ML_DSA_65, pk).verify(msg, sig).is_ok();
    if pk.len() == PK_LEN && sig.len() == SIG_LEN {
        let public = PublicKey::MLDSA65(MlDsa65PublicKey(Box::new(pk.try_into().unwrap())));
        let signature = Signature::from_parts(KeyType::MLDSA65, sig).unwrap();
        assert_eq!(signature.verify(msg, &public), direct);
    }
    direct
}

/// `ml_dsa_65_sign_internal` with the domain-separation prefix `pre` and the randomness `rnd`.
fn sign_internal(sk: &[u8], msg: &[u8], pre: &[u8], rnd: &[u8; 32]) -> Vec<u8> {
    let mut sig = vec![0u8; SIG_LEN];
    let mut n = 0usize;
    let ok = unsafe {
        ml_dsa_65_sign_internal(sk.as_ptr(), sig.as_mut_ptr(), &mut n, msg.as_ptr(), msg.len(), pre.as_ptr(), pre.len(), rnd.as_ptr())
    };
    assert_eq!((ok, n), (1, SIG_LEN));
    sig
}

fn sign_extmu(sk: &[u8], mu: &[u8; 64], pre: &[u8], rnd: &[u8; 32]) -> Vec<u8> {
    let mut sig = vec![0u8; SIG_LEN];
    let mut n = 0usize;
    let ok = unsafe {
        ml_dsa_extmu_65_sign_internal(sk.as_ptr(), sig.as_mut_ptr(), &mut n, mu.as_ptr(), 64, pre.as_ptr(), pre.len(), rnd.as_ptr())
    };
    assert_eq!((ok, n), (1, SIG_LEN));
    sig
}

/// The pure signature `near-crypto` would produce with the randomness `rnd`.
fn sign(key: &Key, msg: &[u8], rnd: &[u8; 32]) -> Vec<u8> {
    let sig = sign_internal(&key.sk, msg, &[0, 0], rnd);
    assert!(verdict(&key.pk, msg, &sig));
    sig
}

fn flip(v: &[u8], at: usize, mask: u8) -> Vec<u8> {
    let mut v = v.to_vec();
    v[at] ^= mask;
    v
}

/// Set the `bits`-bit little-endian field number `index` of `buf` (starting at byte `start`).
fn set_field(buf: &mut [u8], start: usize, index: usize, bits: usize, value: u32) {
    for b in 0..bits {
        let pos = start * 8 + index * bits + b;
        let bit = (value >> b) & 1;
        buf[pos / 8] = (buf[pos / 8] & !(1 << (pos % 8))) | ((bit as u8) << (pos % 8));
    }
}

pub fn mldsa_fixtures(out: &mut Out) {
    let mut rng = Rng::new(0x31d5a);

    // ----- keys -----
    let mut keys: Vec<Key> = vec![];
    let mut seeds: Vec<(String, [u8; 32])> = vec![
        ("zeros".into(), [0u8; 32]),
        ("ones".into(), [0xffu8; 32]),
        ("count".into(), core::array::from_fn(|i| i as u8)),
    ];
    for i in 0..9 {
        seeds.push((format!("random-{i}"), rng.array()));
    }
    for (name, seed) in seeds {
        let key = keygen(&name, seed);
        out.push("keygen", json!({"kind": "keygen", "name": name, "seed": hex(&seed), "public": hex(&key.pk), "secret": hex(&key.sk)}));
        keys.push(key);
    }

    // ----- raw private keys: what `SecretKey::from_str` and `SecretKey::sign` accept -----
    let secret_line = |out: &mut Out, name: String, sk: &[u8]| {
        let direct = PqdsaKeyPair::from_raw_private_key(&ML_DSA_65_SIGNING, sk);
        if sk.len() == SK_LEN {
            let near = format!("ml-dsa-65:{}", bs58::encode(sk).into_string()).parse::<SecretKey>();
            assert_eq!(near.is_ok(), direct.is_ok());
            if let (Ok(n), Ok(d)) = (&near, &direct) {
                assert_eq!(n.public_key().key_data(), AsRef::<[u8]>::as_ref(d.public_key()));
            }
        }
        match direct {
            Ok(kp) => {
                let pk: &[u8] = kp.public_key().as_ref();
                out.push("secret", json!({"kind": "secret", "name": name, "secret": hex(sk), "valid": true, "public": hex(pk)}));
            }
            Err(_) => out.push("secret", json!({"kind": "secret", "name": name, "secret": hex(sk), "valid": false})),
        }
    };
    // Layout: rho 32, K 32, tr 64, s1 5 x 128, s2 6 x 128, t0 6 x 416.
    const S1: usize = 128;
    const S2: usize = S1 + 5 * 128;
    const T0: usize = S2 + 6 * 128;
    for key in &keys[..2] {
        let n = &key.name;
        let sk = &key.sk;
        secret_line(out, format!("{n}/as-generated"), sk);
        secret_line(out, format!("{n}/K-flip"), &flip(sk, 40, 0x10));
        secret_line(out, format!("{n}/rho-flip"), &flip(sk, 3, 0x01));
        secret_line(out, format!("{n}/tr-flip"), &flip(sk, 100, 0x80));
        secret_line(out, format!("{n}/t0-flip"), &flip(sk, T0 + 1000, 0x04));
        secret_line(out, format!("{n}/t0-last-bit"), &flip(sk, SK_LEN - 1, 0x80));
        // A coefficient nibble `eta - s`: 9 to 15 would be -5 to -11.
        for (label, at) in [("s1", S1), ("s2", S2 + 3 * 128)] {
            for nibble in [9u8, 15] {
                let mut v = sk.clone();
                v[at + 5] = (v[at + 5] & 0xf0) | nibble;
                secret_line(out, format!("{n}/{label}-nibble-{nibble}"), &v);
                let mut v = sk.clone();
                v[at + 5] = (v[at + 5] & 0x0f) | (nibble << 4);
                secret_line(out, format!("{n}/{label}-high-nibble-{nibble}"), &v);
            }
            // A coefficient in range but not the generated one: `t0` no longer matches.
            let mut v = sk.clone();
            let old = v[at + 7] & 0x0f;
            v[at + 7] = (v[at + 7] & 0xf0) | (if old == 8 { 0 } else { 8 });
            secret_line(out, format!("{n}/{label}-in-range-change"), &v);
        }
        secret_line(out, format!("{n}/truncated"), &sk[..SK_LEN - 1]);
        let mut longer = sk.clone();
        longer.push(0);
        secret_line(out, format!("{n}/extended"), &longer);
    }
    secret_line(out, "zeros".into(), &vec![0u8; SK_LEN]);
    secret_line(out, "ones".into(), &vec![0xffu8; SK_LEN]);
    secret_line(out, "empty".into(), &[]);

    // ----- signatures with chosen randomness -----
    struct Base {
        key: usize,
        msg: Vec<u8>,
        sig: Vec<u8>,
    }
    let mut bases: Vec<Base> = vec![];
    let long = vec![0x5au8; 100_000];
    let message_set: Vec<(&str, Vec<u8>)> = vec![
        ("empty", vec![]),
        ("abc", b"abc".to_vec()),
        ("32", rng.bytes(32)),
        ("100", rng.bytes(100)),
        ("1000", rng.bytes(1000)),
        ("4096", rng.bytes(4096)),
    ];
    for (i, key) in keys.iter().enumerate() {
        for (j, (label, msg)) in message_set.iter().enumerate() {
            if i >= 6 && ((i + j) % 2 == 1 || j == 5) {
                continue;
            }
            // Zero randomness is the deterministic variant of FIPS 204 algorithm 2.
            let rnd: [u8; 32] = if (i + j) % 3 == 0 { [0u8; 32] } else { rng.array() };
            let sig = sign(key, msg, &rnd);
            out.push("sign", json!({"kind": "sign", "name": format!("{}/{label}", key.name), "key": key.name, "msg": hex(msg), "rnd": hex(&rnd), "sig": hex(&sig)}));
            if i < 4 && (j == 1 || j == 3) {
                bases.push(Base { key: i, msg: msg.clone(), sig });
            }
        }
    }
    // A long message, spelled as a repeated unit.
    {
        let rnd: [u8; 32] = rng.array();
        let sig = sign(&keys[0], &long, &rnd);
        out.push("sign", json!({"kind": "sign", "name": "zeros/long", "key": "zeros", "unit": "5a", "count": long.len(), "rnd": hex(&rnd), "sig": hex(&sig)}));
    }
    // Signatures with the most hints (the `UseHint` path with many ones): a search over messages.
    for key in [&keys[3], &keys[4]] {
        let mut best: Option<(u8, Vec<u8>, [u8; 32], Vec<u8>)> = None;
        for i in 0..400u32 {
            let msg = i.to_le_bytes().to_vec();
            let rnd = [i as u8; 32];
            let sig = sign_internal(&key.sk, &msg, &[0, 0], &rnd);
            let weight = sig[SIG_LEN - 1];
            if best.as_ref().map_or(true, |b| weight > b.0) {
                best = Some((weight, msg, rnd, sig));
            }
        }
        let (weight, msg, rnd, sig) = best.unwrap();
        assert!(verdict(&key.pk, &msg, &sig));
        out.push("sign", json!({"kind": "sign", "name": format!("{}/most-hints-{weight}", key.name), "key": key.name, "msg": hex(&msg), "rnd": hex(&rnd), "sig": hex(&sig)}));
        bases.push(Base { key: keys.iter().position(|k| k.name == key.name).unwrap(), msg, sig });
    }

    // ----- verification -----
    let vline = |out: &mut Out, name: String, key: usize, msg: &[u8], sig: &[u8]| {
        let valid = verdict(&keys[key].pk, msg, sig);
        out.push("verify", json!({"kind": "verify", "name": name, "key": keys[key].name, "msg": hex(msg), "sig": hex(sig), "valid": valid}));
        valid
    };
    let mut accepted = 0;
    for (n, b) in bases.iter().enumerate() {
        let name = |s: &str| format!("{}/{n}/{s}", keys[b.key].name);
        let (key, msg, sig) = (b.key, &b.msg[..], &b.sig[..]);
        accepted += vline(out, name("valid"), key, msg, sig) as usize;
        let mut other = msg.to_vec();
        if other.is_empty() {
            other.push(0);
        } else {
            other[0] ^= 1;
        }
        vline(out, name("msg-flip"), key, &other, sig);
        let mut longer = msg.to_vec();
        longer.push(0);
        vline(out, name("msg-append"), key, &longer, sig);
        if !msg.is_empty() {
            vline(out, name("msg-truncate"), key, &msg[..msg.len() - 1], sig);
        }
        vline(out, name("wrong-key"), (key + 1) % keys.len(), msg, sig);
        for (label, at, mask) in [("c-first", 0, 0x01), ("c-last", C_TILDE - 1, 0x80), ("c-mid", 24, 0x10)] {
            vline(out, name(label), key, msg, &flip(sig, at, mask));
        }
        for (label, at, mask) in [("z-first", C_TILDE, 0x01), ("z-mid", C_TILDE + 1600, 0x40), ("z-last", Z_END - 1, 0x80)] {
            vline(out, name(label), key, msg, &flip(sig, at, mask));
        }
        // `z` coefficients at the edge of the bound `gamma1 - beta`: the field holds `gamma1 - z`.
        for (label, field) in [
            ("z-at-bound", BETA),
            ("z-inside-bound", BETA + 1),
            ("z-at-neg-bound", 2 * GAMMA1 - BETA),
            ("z-inside-neg-bound", 2 * GAMMA1 - BETA - 1),
            ("z-zero-field", 0),
            ("z-max-field", (1 << 20) - 1),
        ] {
            let mut s = sig.to_vec();
            set_field(&mut s, C_TILDE, 0, 20, field);
            vline(out, name(label), key, msg, &s);
        }
        vline(out, name("hint-index-flip"), key, msg, &flip(sig, Z_END, 0x01));
        vline(out, name("hint-count-flip"), key, msg, &flip(sig, SIG_LEN - 1, 0x01));
        vline(out, name("truncated"), key, msg, &sig[..SIG_LEN - 1]);
        let mut extended = sig.to_vec();
        extended.push(0);
        vline(out, name("extended"), key, msg, &extended);
    }
    assert!(accepted >= 6);

    // Malformed hints on a valid prefix (`c~` and `z` of a real signature).
    let b = &bases[1];
    let prefix = &b.sig[..Z_END];
    let hints = |ys: &[(usize, u8)], counts: [u8; 6]| -> Vec<u8> {
        let mut s = prefix.to_vec();
        let mut h = vec![0u8; OMEGA + 6];
        for (i, v) in ys {
            h[*i] = *v;
        }
        h[OMEGA..].copy_from_slice(&counts);
        s.extend(h);
        s
    };
    let many: Vec<(usize, u8)> = (0..OMEGA).map(|i| (i, i as u8)).collect();
    let cases: Vec<(&str, Vec<u8>)> = vec![
        ("hint-none", hints(&[], [0; 6])),
        ("hint-sorted", hints(&[(0, 1), (1, 2), (2, 9)], [2, 2, 3, 3, 3, 3])),
        ("hint-last-index", hints(&[(0, 255)], [1, 1, 1, 1, 1, 1])),
        ("hint-full", hints(&many, [55; 6])),
        ("hint-full-last-poly", hints(&many, [0, 0, 0, 0, 0, 55])),
        ("hint-unsorted", hints(&[(0, 7), (1, 3)], [2, 2, 2, 2, 2, 2])),
        ("hint-duplicate", hints(&[(0, 3), (1, 3)], [2, 2, 2, 2, 2, 2])),
        ("hint-across-polys-not-sorted", hints(&[(0, 9), (1, 3)], [1, 2, 2, 2, 2, 2])),
        ("hint-counts-decrease", hints(&[(0, 1), (1, 2)], [2, 1, 2, 2, 2, 2])),
        ("hint-count-56", hints(&[], [56; 6])),
        ("hint-count-255", hints(&[], [255; 6])),
        ("hint-last-count-56", hints(&[], [0, 0, 0, 0, 0, 56])),
        ("hint-padding-nonzero", hints(&[(54, 1)], [0; 6])),
        ("hint-trailing-nonzero", hints(&[(0, 1), (1, 2), (2, 9)], [2, 2, 2, 2, 2, 2])),
        ("hint-counts-short", hints(&[(0, 4), (1, 6)], [1, 1, 1, 1, 1, 1])),
        ("hint-padding-last-byte", hints(&[(OMEGA - 1, 77)], [0; 6])),
    ];
    for (label, s) in &cases {
        for (n, base) in [&bases[1], &bases[bases.len() - 1]].iter().enumerate() {
            let mut s = s.clone();
            s[..Z_END].copy_from_slice(&base.sig[..Z_END]);
            vline(out, format!("{label}/{n}"), base.key, &base.msg, &s);
        }
    }

    // The base signature with its hints replaced by none: valid structure, a different `w1`.
    // Other lengths of signature, of key and of message.
    let b = &bases[0];
    for (label, s) in [("sig-empty", vec![]), ("sig-3308-zeros", vec![0u8; 3308]), ("sig-3310-zeros", vec![0u8; 3310]), ("sig-double", [b.sig.clone(), b.sig.clone()].concat())] {
        vline(out, label.to_string(), b.key, &b.msg, &s);
    }
    for (label, s) in [("sig-zeros", vec![0u8; SIG_LEN]), ("sig-ones", vec![0xffu8; SIG_LEN])] {
        vline(out, label.to_string(), b.key, &b.msg, &s);
    }
    for n in 0..16 {
        let s = rng.bytes(SIG_LEN);
        vline(out, format!("sig-random-{n}"), n % keys.len(), &b.msg, &s);
    }
    // Key variants (literal keys): the key bytes are not a named key.
    let kv = |out: &mut Out, name: &str, pk: &[u8], msg: &[u8], sig: &[u8]| {
        let valid = verdict(pk, msg, sig);
        out.push("verify", json!({"kind": "verify", "name": name, "public": hex(pk), "msg": hex(msg), "sig": hex(sig), "valid": valid}));
    };
    let pk = &keys[b.key].pk;
    kv(out, "pk-rho-flip", &flip(pk, 5, 0x02), &b.msg, &b.sig);
    kv(out, "pk-t1-flip", &flip(pk, 1000, 0x08), &b.msg, &b.sig);
    kv(out, "pk-last-flip", &flip(pk, PK_LEN - 1, 0x80), &b.msg, &b.sig);
    kv(out, "pk-zeros", &vec![0u8; PK_LEN], &b.msg, &b.sig);
    kv(out, "pk-ones", &vec![0xffu8; PK_LEN], &b.msg, &b.sig);
    kv(out, "pk-truncated", &pk[..PK_LEN - 1], &b.msg, &b.sig);
    kv(out, "pk-extended", &[pk.clone(), vec![0]].concat(), &b.msg, &b.sig);
    kv(out, "pk-empty", &[], &b.msg, &b.sig);
    kv(out, "pk-valid-literal", pk, &b.msg, &b.sig);

    // Signatures made in the other modes of FIPS 204 and AWS-LC: `near-crypto` verifies the pure
    // mode with an empty context only, so each of these must be rejected.
    let key = &keys[2];
    let msg = b"the same message".to_vec();
    let rnd: [u8; 32] = rng.array();
    let mode = |out: &mut Out, label: &str, sig: Vec<u8>, msg: &[u8]| {
        let valid = verdict(&key.pk, msg, &sig);
        out.push("verify", json!({"kind": "verify", "name": format!("mode/{label}"), "key": key.name, "msg": hex(msg), "sig": hex(&sig), "valid": valid}));
    };
    mode(out, "pure-empty-context", sign_internal(&key.sk, &msg, &[0, 0], &rnd), &msg);
    for ctx in [&b"a"[..], b"abc", &[7u8; 255]] {
        let mut pre = vec![0u8, ctx.len() as u8];
        pre.extend(ctx);
        mode(out, &format!("pure-context-{}", ctx.len()), sign_internal(&key.sk, &msg, &pre, &rnd), &msg);
    }
    mode(out, "internal-no-prefix", sign_internal(&key.sk, &msg, &[], &rnd), &msg);
    {
        // HashML-DSA with SHA-256: prefix 0x01, |ctx| = 0, the OID of SHA-256, the digest.
        use sha2::Digest;
        let digest = sha2::Sha256::digest(&msg);
        let mut pre = vec![1u8, 0, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01];
        pre.extend(digest.iter());
        mode(out, "hash-ml-dsa-sha256", sign_internal(&key.sk, &[], &pre, &rnd), &msg);
        mode(out, "hash-ml-dsa-sha256-of-digest", sign_internal(&key.sk, &[], &pre, &rnd), &digest);
    }
    {
        // ExternalMu: the signature covers a 64-byte `mu`, here SHAKE256(tr || 0 || 0 || msg).
        let tr = shake("shake256", &key.pk, 64);
        let mu: [u8; 64] = shake("shake256", &[tr.clone(), vec![0, 0], msg.clone()].concat(), 64).try_into().unwrap();
        let sig = sign_extmu(&key.sk, &mu, &[], &rnd);
        mode(out, "external-mu-of-msg", sig.clone(), &msg);
        mode(out, "external-mu-as-msg", sig, &mu);
    }

    // The on-trie identifier of a public key: SHA3-256 of a domain tag and the key
    // (`MlDsa65PublicKey::to_public_key_handle`).
    let handle = |pk: &[u8]| -> String { hex(&MlDsa65PublicKey(Box::new(pk.try_into().unwrap())).to_public_key_handle().0) };
    for key in &keys {
        out.push("handle", json!({"kind": "handle", "name": key.name, "key": key.name, "handle": handle(&key.pk)}));
    }
    for (name, pk) in [("zeros", vec![0u8; PK_LEN]), ("ones", vec![0xffu8; PK_LEN])] {
        out.push("handle", json!({"kind": "handle", "name": name, "public": hex(&pk), "handle": handle(&pk)}));
    }
}
