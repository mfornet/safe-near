//! Generates the crypto conformance fixtures for `near-lean/crypto`. `crypto-fixtures <out dir>`
//! writes `hash.jsonl`, `ed25519.jsonl` and `manifest.json`. The output is a pure function of the
//! code and the locked dependencies.
//!
//! * Hashes come from the crates nearcore uses: `sha2` (SHA-256 through `near-crypto`'s
//!   `CryptoHash`, and SHA-512), `sha3` (`Keccak256`, `Keccak512`, the legacy padding of the VM host
//!   functions) and `ripemd`.
//! * Ed25519 verdicts come from `near_crypto::Signature::verify`, which calls
//!   `ed25519_dalek::VerifyingKey::from_bytes` and the non-strict `Verifier::verify`. Public key
//!   decoding verdicts come from `ed25519_dalek::VerifyingKey::from_bytes` and key pairs from
//!   `SigningKey::from_keypair_bytes`. `curve25519-dalek` builds the adversarial inputs
//!   (small-order and mixed-order points); the verdict on each is always the crates' own.

use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT, EIGHT_TORSION};
use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::scalar::Scalar;
use near_crypto::{ED25519PublicKey, ED25519SecretKey, KeyType, PublicKey, SecretKey, Signature};
use near_primitives::hash::CryptoHash;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use blake2::{Blake2b512, Blake2bVar};
use ripemd::Ripemd160;
use serde_json::{json, Value};
use sha2::{Digest, Sha512};
use sha3::{Keccak256, Keccak512};
use std::collections::BTreeMap;
use std::path::PathBuf;

mod crypto_secp;
mod crypto_vrf;

const SEED: u64 = 0x4e45_4152_0000_0002;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

struct Rng(ChaCha8Rng);

impl Rng {
    fn new(label: u64) -> Rng {
        Rng(ChaCha8Rng::seed_from_u64(SEED ^ label.wrapping_mul(0x9e37_79b9_7f4a_7c15)))
    }

    fn bytes(&mut self, n: usize) -> Vec<u8> {
        let mut v = vec![0u8; n];
        self.0.fill_bytes(&mut v);
        v
    }

    fn array<const N: usize>(&mut self) -> [u8; N] {
        let mut v = [0u8; N];
        self.0.fill_bytes(&mut v);
        v
    }
}

#[derive(Default)]
struct Out {
    lines: Vec<String>,
    counts: BTreeMap<String, usize>,
}

impl Out {
    fn push(&mut self, kind: &str, v: Value) {
        *self.counts.entry(kind.to_string()).or_default() += 1;
        self.lines.push(serde_json::to_string(&v).unwrap());
    }

    fn write(&self, path: PathBuf) {
        std::fs::write(path, self.lines.join("\n") + "\n").unwrap();
    }
}

// ---------------------------------------------------------------------------------------------
// Hashes

fn digest(alg: &str, msg: &[u8]) -> Vec<u8> {
    match alg {
        // The hash nearcore uses everywhere (`CryptoHash::hash_bytes`).
        "sha256" => CryptoHash::hash_bytes(msg).as_ref().to_vec(),
        "sha512" => Sha512::digest(msg).to_vec(),
        "keccak256" => Keccak256::digest(msg).to_vec(),
        "keccak512" => Keccak512::digest(msg).to_vec(),
        "ripemd160" => Ripemd160::digest(msg).to_vec(),
        // `near_crypto::vrf` hashes with BLAKE2b of 32 and of 64 bytes.
        "blake2b256" => {
            use blake2::digest::{Update, VariableOutput};
            let mut h = Blake2bVar::new(32).unwrap();
            h.update(msg);
            let mut out = vec![0u8; 32];
            h.finalize_variable(&mut out).unwrap();
            out
        }
        "blake2b512" => Blake2b512::digest(msg).to_vec(),
        _ => unreachable!(),
    }
}

const ALGS: [&str; 7] = ["sha256", "sha512", "keccak256", "keccak512", "ripemd160", "blake2b256", "blake2b512"];

fn hashes(out: &mut Out) {
    // Sanity check against the published values, so a wrong crate cannot silently pass.
    assert_eq!(hex(&digest("sha256", b"abc")), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    assert_eq!(hex(&digest("keccak256", b"")), "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
    assert_eq!(hex(&digest("ripemd160", b"abc")), "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc");
    assert_eq!(hex(&digest("blake2b256", b"abc")), "bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319");
    assert_eq!(hex(&digest("blake2b512", b"abc")), "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923");

    let lengths = [
        0usize, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 55, 56, 57, 63, 64, 65, 71, 72, 73, 111,
        112, 113, 119, 120, 121, 127, 128, 129, 135, 136, 137, 143, 144, 145, 199, 200, 201, 255, 256,
        257, 271, 272, 273, 511, 512, 513, 1000, 1023, 1024, 1025, 4095, 4096, 4097, 20000,
    ];
    let boundaries = [55usize, 56, 64, 111, 112, 128, 135, 136, 137];
    let classics: [(&str, &[u8]); 3] = [
        ("abc", b"abc"),
        ("abcdbcdecdef", b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
        ("abcdefgh", b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"),
    ];
    for alg in ALGS {
        let mut rng = Rng::new(fnv(alg));
        for (name, msg) in classics {
            out.push("hash", json!({"alg": alg, "name": name, "msg": hex(msg), "digest": hex(&digest(alg, msg))}));
        }
        for n in lengths {
            let msg = rng.bytes(n);
            out.push("hash", json!({"alg": alg, "name": format!("random-{n}"), "msg": hex(&msg), "digest": hex(&digest(alg, &msg))}));
        }
        for n in boundaries {
            for (pat, b) in [("zeros", 0u8), ("ones", 0xff)] {
                let msg = vec![b; n];
                out.push("hash", json!({"alg": alg, "name": format!("{pat}-{n}"), "msg": hex(&msg), "digest": hex(&digest(alg, &msg))}));
            }
        }
        // One million `a`, the standard long vector: spelled as a repeated unit.
        let million = vec![b'a'; 1_000_000];
        out.push("hash", json!({"alg": alg, "name": "million-a", "unit": "61", "count": 1_000_000, "digest": hex(&digest(alg, &million))}));
    }
}

fn fnv(s: &str) -> u64 {
    s.bytes().fold(0xcbf29ce484222325, |h, b| (h ^ b as u64).wrapping_mul(0x100000001b3))
}

// ---------------------------------------------------------------------------------------------
// Ed25519

const P_LE: [u8; 32] = {
    let mut b = [0xffu8; 32];
    b[0] = 0xed;
    b[31] = 0x7f;
    b
};

/// The group order `ℓ = 2^252 + 27742317777372353535851937790883648493`, little-endian.
const ELL: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0x10,
];

fn near_verify(pk: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
    let signature = Signature::from_parts(KeyType::ED25519, sig).unwrap();
    signature.verify(msg, &PublicKey::ED25519(ED25519PublicKey(*pk)))
}

fn dalek_decodes(pk: &[u8; 32]) -> bool {
    ed25519_dalek::VerifyingKey::from_bytes(pk).is_ok()
}

fn keypair_of(seed: &[u8; 32]) -> [u8; 64] {
    ed25519_dalek::SigningKey::from_bytes(seed).to_keypair_bytes()
}

fn near_sign(keypair: &[u8; 64], msg: &[u8]) -> [u8; 64] {
    let sk = SecretKey::ED25519(ED25519SecretKey(*keypair));
    match sk.sign(msg) {
        Signature::ED25519(s) => s.to_bytes(),
        _ => unreachable!(),
    }
}

fn near_public(keypair: &[u8; 64]) -> [u8; 32] {
    match SecretKey::ED25519(ED25519SecretKey(*keypair)).public_key() {
        PublicKey::ED25519(k) => k.0,
        _ => unreachable!(),
    }
}

/// `a + b` as 256-bit little-endian integers; `None` on overflow.
fn add256(a: &[u8; 32], b: &[u8; 32]) -> Option<[u8; 32]> {
    let mut out = [0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let s = a[i] as u16 + b[i] as u16 + carry;
        out[i] = s as u8;
        carry = s >> 8;
    }
    if carry == 0 { Some(out) } else { None }
}

fn set_bit(b: &mut [u8], bit: usize) {
    b[bit / 8] ^= 1 << (bit % 8);
}

fn verify_line(out: &mut Out, name: &str, pk: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
    let valid = near_verify(pk, msg, sig);
    out.push(
        "verify",
        json!({"kind": "verify", "name": name, "public": hex(pk), "msg": hex(msg), "sig": hex(sig), "valid": valid}),
    );
    valid
}

/// The fourteen encodings of the eight small-order points: eight canonical ones and six that
/// ed25519-dalek accepts anyway (`y ≥ p`, or a sign bit on `x = 0`).
fn small_order_encodings() -> Vec<[u8; 32]> {
    let mut v: Vec<[u8; 32]> = EIGHT_TORSION.iter().map(|p| p.compress().to_bytes()).collect();
    let canonical = v.clone();
    let mut extra = vec![];
    for y in [0u8, 1] {
        // y + p is below 2^255 only for y < 19.
        let mut b = P_LE;
        b[0] = 0xed + y;
        extra.push(b);
        let mut c = b;
        c[31] |= 0x80;
        extra.push(c);
    }
    // x = 0 (identity and −1) with the sign bit set.
    for e in [canonical.iter().find(|b| **b == identity_bytes()).unwrap(), canonical.iter().find(|b| **b == minus_one_bytes()).unwrap()] {
        let mut c = *e;
        c[31] |= 0x80;
        extra.push(c);
    }
    for e in extra {
        if !v.contains(&e) {
            v.push(e);
        }
    }
    for e in &v {
        let pt = CompressedEdwardsY(*e).decompress().expect("small-order encoding decodes");
        assert!(pt.is_small_order());
        assert!(dalek_decodes(e));
    }
    v
}

fn identity_bytes() -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0] = 1;
    b
}

fn minus_one_bytes() -> [u8; 32] {
    let mut b = P_LE;
    b[0] = 0xec;
    b
}

fn ed25519(out: &mut Out) {
    let mut rng = Rng::new(0xed25519);

    // Key pairs. The RFC 8032 vectors pin the derivation to the standard.
    // The published public keys are checked for the vectors whose values are certain.
    let rfc: [(&str, Option<&str>); 5] = [
        ("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60", Some("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")),
        ("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb", Some("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")),
        ("c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7", None),
        ("f5e5767cf153319517630f226876b86c8160cc583bc013744c6bf255f5cc0ee5", Some("278117fc144c72340f67d0f2316e8386ceffbf2b2428c9c51fef7c597f1d426e")),
        ("833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42", Some("ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf")),
    ];
    let mut seeds: Vec<(String, [u8; 32])> = vec![];
    for (i, (s, pk)) in rfc.iter().enumerate() {
        let seed: [u8; 32] = unhex(s).try_into().unwrap();
        if let Some(pk) = pk {
            assert_eq!(hex(&keypair_of(&seed)[32..]), *pk);
        }
        seeds.push((format!("rfc8032-{}", i + 1), seed));
    }
    seeds.push(("zero".into(), [0; 32]));
    seeds.push(("ff".into(), [0xff; 32]));
    // near-crypto's `SecretKey::from_seed(KeyType::ED25519, "test")`: the string padded with spaces.
    let mut padded = [b' '; 32];
    padded[..4].copy_from_slice(b"test");
    seeds.push(("near-test-seed".into(), padded));
    for i in 0..20 {
        seeds.push((format!("random-{i}"), rng.array()));
    }
    for (name, seed) in &seeds {
        let kp = keypair_of(seed);
        assert_eq!(near_public(&kp), kp[32..]);
        out.push(
            "keypair",
            json!({"kind": "keypair", "name": name, "seed": hex(seed), "public": hex(&kp[32..]), "keypair": hex(&kp)}),
        );
    }

    // `SigningKey::from_keypair_bytes`: the public half must be the derived one, byte for byte.
    let (_, seed0) = &seeds[0];
    let kp0 = keypair_of(seed0);
    let mut cases: Vec<(String, [u8; 64])> = vec![("valid".into(), kp0)];
    for bit in [0usize, 1, 7, 100, 254, 255] {
        let mut k = kp0;
        set_bit(&mut k[32..], bit);
        cases.push((format!("public-bit-{bit}"), k));
    }
    let mut k = kp0;
    k[32..].copy_from_slice(&keypair_of(&seeds[1].1)[32..]);
    cases.push(("other-public".into(), k));
    let mut k = kp0;
    k[32..].copy_from_slice(&identity_bytes());
    cases.push(("identity-public".into(), k));
    let mut k = kp0;
    k[32..].fill(0xff);
    cases.push(("ff-public".into(), k));
    let mut k = kp0;
    k[32..].fill(0);
    cases.push(("zero-public".into(), k));
    // A non-canonical encoding of the public key is a different byte string: rejected.
    let mut k = keypair_of(&seeds[3].1);
    k[63] ^= 0x80;
    cases.push(("sign-bit-flipped".into(), k));
    let mut k = kp0;
    k[0] ^= 1;
    cases.push(("seed-bit-0".into(), k));
    for (name, kp) in cases {
        let valid = ed25519_dalek::SigningKey::from_keypair_bytes(&kp).is_ok();
        out.push("keypair-check", json!({"kind": "keypair-check", "name": name, "keypair": hex(&kp), "valid": valid}));
    }

    // Signatures by near-crypto, which every implementation must reproduce exactly (RFC 8032 is
    // deterministic).
    let sign_lengths = [0usize, 1, 2, 31, 32, 33, 63, 64, 65, 127, 128, 129, 1000];
    let mut signed: Vec<([u8; 32], [u8; 32], Vec<u8>, [u8; 64])> = vec![];
    for (i, (name, seed)) in seeds.iter().enumerate() {
        let kp = keypair_of(seed);
        let pk: [u8; 32] = kp[32..].try_into().unwrap();
        let n = sign_lengths[i % sign_lengths.len()];
        let msg = rng.bytes(n);
        let sig = near_sign(&kp, &msg);
        assert!(near_verify(&pk, &msg, &sig));
        out.push(
            "sign",
            json!({"kind": "sign", "name": format!("{name}-{n}"), "seed": hex(seed), "public": hex(&pk), "msg": hex(&msg), "sig": hex(&sig)}),
        );
        signed.push((*seed, pk, msg, sig));
    }
    // The RFC 8032 test 1 signature, as published.
    let empty_sig = near_sign(&keypair_of(&seeds[0].1), b"");
    assert_eq!(hex(&empty_sig), "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b");
    out.push(
        "sign",
        json!({"kind": "sign", "name": "rfc8032-1-empty", "seed": hex(&seeds[0].1), "public": hex(&keypair_of(&seeds[0].1)[32..]), "msg": "", "sig": hex(&empty_sig)}),
    );

    // Verification: accepts, then edits of valid signatures.
    for (idx, (_, pk, msg, sig)) in signed.iter().enumerate().take(6) {
        let tag = format!("key{idx}");
        assert!(verify_line(out, &format!("{tag}/valid"), pk, msg, sig));
        let mut wrong = msg.clone();
        if wrong.is_empty() { wrong.push(0) } else { wrong[0] ^= 1 }
        assert!(!verify_line(out, &format!("{tag}/wrong-message"), pk, &wrong, sig));
        let mut longer = msg.clone();
        longer.push(0);
        verify_line(out, &format!("{tag}/message-extended"), pk, &longer, sig);
        for bit in [0usize, 1, 7, 8, 63, 100, 200, 248, 254, 255] {
            let mut s = *sig;
            set_bit(&mut s[..32], bit);
            verify_line(out, &format!("{tag}/R-bit-{bit}"), pk, msg, &s);
        }
        for bit in [0usize, 1, 7, 8, 100, 200, 251, 252, 253, 254, 255] {
            let mut s = *sig;
            set_bit(&mut s[32..], bit);
            verify_line(out, &format!("{tag}/S-bit-{bit}"), pk, msg, &s);
        }
        for bit in [0usize, 1, 8, 100, 254, 255] {
            let mut k = *pk;
            set_bit(&mut k, bit);
            verify_line(out, &format!("{tag}/A-bit-{bit}"), &k, msg, sig);
        }
        // Another key's public key.
        let other = signed[(idx + 1) % signed.len()].1;
        assert!(!verify_line(out, &format!("{tag}/other-key"), &other, msg, sig));
        // S + k·ℓ is the same scalar mod ℓ and must be rejected whenever it fits.
        let ell = ELL;
        let s: [u8; 32] = sig[32..].try_into().unwrap();
        let mut t = s;
        for k in 1..=15u32 {
            match add256(&t, &ell) {
                Some(n) => t = n,
                None => break,
            }
            let mut sg = *sig;
            sg[32..].copy_from_slice(&t);
            if matches!(k, 1 | 2 | 4 | 8 | 15) {
                assert!(!verify_line(out, &format!("{tag}/S-plus-{k}-ell"), pk, msg, &sg));
            }
        }
        // swapped halves
        let mut sg = [0u8; 64];
        sg[..32].copy_from_slice(&sig[32..]);
        sg[32..].copy_from_slice(&sig[..32]);
        verify_line(out, &format!("{tag}/halves-swapped"), pk, msg, &sg);
    }

    // The scalar boundary on a valid R: S = 0, ℓ − 1, ℓ, ℓ + 1, 2^253 − 1, 2^256 − 1.
    let (_, pk, msg, sig) = &signed[3];
    let ell = ELL;
    let mut ell_minus_1 = ell;
    ell_minus_1[0] -= 1;
    let mut ell_plus_1 = ell;
    ell_plus_1[0] += 1;
    let mut top253 = [0xffu8; 32];
    top253[31] = 0x1f;
    for (name, s) in [("zero", [0u8; 32]), ("ell-1", ell_minus_1), ("ell", ell), ("ell+1", ell_plus_1), ("2^253-1", top253), ("2^256-1", [0xff; 32])] {
        let mut sg = *sig;
        sg[32..].copy_from_slice(&s);
        verify_line(out, &format!("scalar/{name}"), pk, msg, &sg);
    }

    // Small-order public keys and R, the ZIP 215 matrix: 14 × 14 encodings, S = 0, message "Zcash".
    let small = small_order_encodings();
    assert_eq!(small.len(), 14);
    for (i, r) in small.iter().enumerate() {
        out.push("pubkey", json!({"kind": "pubkey", "name": format!("small-order-{i}"), "public": hex(r), "valid": true}));
    }
    for (i, a) in small.iter().enumerate() {
        for (j, r) in small.iter().enumerate() {
            let mut sg = [0u8; 64];
            sg[..32].copy_from_slice(r);
            verify_line(out, &format!("zip215/A{i}-R{j}"), a, b"Zcash", &sg);
        }
    }
    // The identity key with the identity R and S = 0 verifies every message (cofactorless
    // equation `[0]B − [k]O = O`).
    let mut id_sig = [0u8; 64];
    id_sig[0] = 1;
    for (i, msg) in [&b""[..], b"a", b"another message", &[0u8; 100][..]].iter().enumerate() {
        assert!(verify_line(out, &format!("identity/any-message-{i}"), &identity_bytes(), msg, &id_sig));
    }

    // Small-order keys with a real accept: for each torsion A and canonical torsion R, search
    // messages until `[−k]A = R` (S = 0). The crates decide each verdict.
    let torsion: Vec<[u8; 32]> = EIGHT_TORSION.iter().map(|p| p.compress().to_bytes()).collect();
    for (i, a) in torsion.iter().enumerate() {
        for (j, r) in torsion.iter().enumerate() {
            let mut sg = [0u8; 64];
            sg[..32].copy_from_slice(r);
            let mut found = None;
            for m in 0..512u32 {
                let msg = format!("torsion-{i}-{j}-{m}").into_bytes();
                if near_verify(a, &msg, &sg) {
                    found = Some(msg);
                    break;
                }
            }
            if let Some(msg) = found {
                assert!(verify_line(out, &format!("torsion-accept/A{i}-R{j}"), a, &msg, &sg));
                let mut other = msg.clone();
                other.push(b'!');
                verify_line(out, &format!("torsion-accept/A{i}-R{j}-other-message"), a, &other, &sg);
            }
        }
    }

    // Mixed-order keys A' = A + T. With k = H(R ‖ A' ‖ M) ≡ 0 (mod 8) the signature made with the
    // scalar of A verifies for A', so a key outside the prime-order subgroup is accepted; for any
    // other k it is rejected.
    for idx in 1..8usize {
        let torsion_point = &EIGHT_TORSION[idx];
        let seed = &seeds[10 + idx].1;
        let h = Sha512::digest(seed);
        let mut a_bytes: [u8; 32] = h[..32].try_into().unwrap();
        a_bytes[0] &= 248;
        a_bytes[31] &= 127;
        a_bytes[31] |= 64;
        let a = Scalar::from_bytes_mod_order(a_bytes);
        let a_point = a * ED25519_BASEPOINT_POINT;
        let mixed: EdwardsPoint = a_point + torsion_point;
        let mixed_bytes = mixed.compress().to_bytes();
        let r_scalar = Scalar::from_bytes_mod_order_wide(&Sha512::digest(format!("mixed-r-{idx}")).into());
        let r_bytes = (r_scalar * ED25519_BASEPOINT_POINT).compress().to_bytes();
        let (mut accepted, mut rejected) = (false, false);
        for m in 0..400u32 {
            let msg = format!("mixed-{idx}-{m}").into_bytes();
            let mut hasher = Sha512::new();
            hasher.update(r_bytes);
            hasher.update(mixed_bytes);
            hasher.update(&msg);
            let k = Scalar::from_bytes_mod_order_wide(&hasher.finalize().into());
            let s = r_scalar + k * a;
            let mut sg = [0u8; 64];
            sg[..32].copy_from_slice(&r_bytes);
            sg[32..].copy_from_slice(&s.to_bytes());
            let k_mod_8 = k.to_bytes()[0] & 7;
            if k_mod_8 == 0 && !accepted {
                assert!(verify_line(out, &format!("mixed-order/T{idx}-accept"), &mixed_bytes, &msg, &sg));
                accepted = true;
            } else if k_mod_8 != 0 && !rejected && (k_mod_8 * torsion_order_factor(idx)) % 8 != 0 {
                assert!(!verify_line(out, &format!("mixed-order/T{idx}-reject"), &mixed_bytes, &msg, &sg));
                rejected = true;
            }
            if accepted && rejected {
                break;
            }
        }
        assert!(accepted && rejected, "mixed-order case {idx}");
    }

    // Public key decoding (`VerifyingKey::from_bytes`).
    let mut pubkeys: Vec<(String, [u8; 32])> = vec![];
    pubkeys.push(("basepoint".into(), ED25519_BASEPOINT_POINT.compress().to_bytes()));
    pubkeys.push(("zero".into(), [0; 32]));
    pubkeys.push(("ff".into(), [0xff; 32]));
    for y in 0..19u8 {
        for sign in [0u8, 0x80] {
            // y + p, a non-canonical encoding of y.
            let mut b = P_LE;
            b[0] = 0xed + y;
            b[31] |= sign;
            pubkeys.push((format!("y-plus-p-{y}-s{}", sign >> 7), b));
        }
    }
    for y in 2..40u8 {
        let mut b = [0u8; 32];
        b[0] = y;
        pubkeys.push((format!("small-y-{y}"), b));
    }
    for sign in [0u8, 0x80] {
        let mut b = P_LE;
        b[0] = 0xec;
        b[31] |= sign;
        pubkeys.push((format!("y-p-minus-1-s{}", sign >> 7), b));
        let mut b = P_LE;
        b[0] = 0xec - 1;
        b[31] |= sign;
        pubkeys.push((format!("y-p-minus-2-s{}", sign >> 7), b));
    }
    for i in 0..120 {
        pubkeys.push((format!("random-{i}"), rng.array()));
    }
    for (_, kp) in seeds.iter().map(|(n, s)| (n, keypair_of(s))).take(8) {
        let pk: [u8; 32] = kp[32..].try_into().unwrap();
        pubkeys.push(("derived".into(), pk));
        let mut flipped = pk;
        flipped[31] ^= 0x80;
        pubkeys.push(("derived-sign-flipped".into(), flipped));
    }
    for (name, pk) in &pubkeys {
        out.push("pubkey", json!({"kind": "pubkey", "name": name, "public": hex(pk), "valid": dalek_decodes(pk)}));
    }
    // Both signs of x = 0 and the keys that exist only with an odd root: make sure the matrix
    // above produced both verdicts.
    let valid = pubkeys.iter().filter(|(_, p)| dalek_decodes(p)).count();
    assert!(valid > 20 && valid < pubkeys.len() - 20);
}

/// The multiplier by which `k` acts on a torsion point of index `idx` in `EIGHT_TORSION` (`k·T`
/// is the identity iff `k · idx` is a multiple of 8, as `EIGHT_TORSION[i] = i · T1`).
fn torsion_order_factor(idx: usize) -> u8 {
    idx as u8
}

fn main() {
    let dir = PathBuf::from(std::env::args().nth(1).expect("usage: crypto-fixtures <out dir>"));
    std::fs::create_dir_all(&dir).unwrap();
    let mut h = Out::default();
    hashes(&mut h);
    h.write(dir.join("hash.jsonl"));
    let mut e = Out::default();
    ed25519(&mut e);
    e.write(dir.join("ed25519.jsonl"));
    let mut s = Out::default();
    crypto_secp::secp256k1(&mut s);
    s.write(dir.join("secp256k1.jsonl"));
    let mut v = Out::default();
    crypto_vrf::vrf(&mut v);
    v.write(dir.join("vrf.jsonl"));
    let mut counts = BTreeMap::new();
    counts.insert("hash.jsonl", &h.counts);
    counts.insert("ed25519.jsonl", &e.counts);
    counts.insert("secp256k1.jsonl", &s.counts);
    counts.insert("vrf.jsonl", &v.counts);
    let manifest = json!({
        "crates": "near-crypto =0.37.4, secp256k1 =0.27.0 (libsecp256k1 of secp256k1-sys 0.8.2), ed25519-dalek =2.2.0, curve25519-dalek =4.1.3, sha2 =0.10.9, sha3 =0.10.9, ripemd 0.1, blake2 0.10",
        "verifier": "near_crypto::Signature::verify -> ed25519_dalek::VerifyingKey::from_bytes + Verifier::verify (non-strict, no legacy_compatibility); SECP256K1: recovery id and r, s parsed by secp256k1::RecoverableSignature::from_compact, then secp256k1_ecdsa_verify (low s only); VM ecrecover: Secp256K1Signature::check_signature_values then recover; VRF: near_crypto::vrf",
        "seed": format!("{SEED:#018x}"),
        "files": counts,
    });
    std::fs::write(dir.join("manifest.json"), serde_json::to_string_pretty(&manifest).unwrap() + "\n").unwrap();
}
