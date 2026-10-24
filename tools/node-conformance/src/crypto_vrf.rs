//! VRF and ristretto255 fixtures: `near_crypto::vrf` (keys, values, proofs, verification),
//! `near_crypto::key_conversion` (the ed25519 to ristretto key conversion block producers go
//! through) and the `curve25519-dalek` 4.1.3 ristretto operations the VRF is built on.
//! Verdicts always come from the crates.

use super::{hex, Out, Rng};
use curve25519_dalek::constants::{RISTRETTO_BASEPOINT_POINT, RISTRETTO_BASEPOINT_TABLE};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use near_crypto::key_conversion::{convert_public_key, convert_secret_key};
use near_crypto::vrf::{Proof, PublicKey, SecretKey, Value};
use near_crypto::{ED25519PublicKey, ED25519SecretKey};
use near_primitives::hash::CryptoHash;
use serde_json::{json, Value as Json};

/// The group order, little-endian.
const ELL: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0x10,
];
const P_LE: [u8; 32] = {
    let mut b = [0xffu8; 32];
    b[0] = 0xed;
    b[31] = 0x7f;
    b
};

/// `a + b` as 256-bit little-endian integers, wrapping.
fn add256(a: &[u8; 32], b: &[u8; 32]) -> ([u8; 32], bool) {
    let mut out = [0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let s = a[i] as u16 + b[i] as u16 + carry;
        out[i] = s as u8;
        carry = s >> 8;
    }
    (out, carry != 0)
}

fn set_bit(b: &mut [u8], bit: usize) {
    b[bit / 8] ^= 1 << (bit % 8);
}

fn vrf_secret(seed: &[u8; 32]) -> (SecretKey, [u8; 64]) {
    let kp = ed25519_dalek::SigningKey::from_bytes(seed).to_keypair_bytes();
    (convert_secret_key(&ED25519SecretKey(kp)), kp)
}

fn bytes32(s: &SecretKey) -> [u8; 32] {
    <[u8; 32]>::from(s)
}

fn pk_bytes(p: &PublicKey) -> [u8; 32] {
    <[u8; 32]>::from(p)
}

fn valid(pk: &PublicKey, input: &[u8], value: &[u8; 32], proof: &[u8; 64]) -> bool {
    pk.is_vrf_valid(&input.to_vec(), &Value(*value), &Proof(*proof))
}

fn canonical(b: &[u8; 32]) -> Option<Scalar> {
    Option::from(Scalar::from_canonical_bytes(*b))
}

pub fn vrf(out: &mut Out) {
    let mut rng = Rng::new(0x57f);

    // ----- ristretto255 -----
    // Encodings of small multiples of the base point (valid), then edits and random strings.
    let mut encodings: Vec<(String, [u8; 32])> = vec![];
    let mut p = RISTRETTO_BASEPOINT_POINT * Scalar::ZERO;
    for i in 0..20 {
        encodings.push((format!("multiple-{i}"), p.compress().to_bytes()));
        p += RISTRETTO_BASEPOINT_POINT;
    }
    let base_enc = RISTRETTO_BASEPOINT_POINT.compress().to_bytes();
    for bit in [0usize, 1, 2, 3, 8, 50, 100, 200, 254, 255] {
        let mut e = base_enc;
        set_bit(&mut e, bit);
        encodings.push((format!("base-bit-{bit}"), e));
    }
    // s = p + k (non-canonical) for small k, with the sign bit, s = p - 1 (odd), s >= 2^255
    for k in 0..19u8 {
        let mut e = P_LE;
        e[0] = 0xed + k;
        encodings.push((format!("p-plus-{k}"), e));
    }
    for k in 1..4u8 {
        let mut e = P_LE;
        e[0] = 0xed - k;
        encodings.push((format!("p-minus-{k}"), e));
    }
    encodings.push(("ff".into(), [0xff; 32]));
    encodings.push(("zero".into(), [0; 32]));
    let mut one = [0u8; 32];
    one[0] = 1;
    encodings.push(("one".into(), one));
    for s in 2..40u8 {
        let mut e = [0u8; 32];
        e[0] = s;
        encodings.push((format!("small-{s}"), e));
    }
    for i in 0..150 {
        let mut e: [u8; 32] = rng.array();
        if i % 2 == 0 {
            e[31] &= 0x7f;
            e[0] &= 0xfe;
        }
        encodings.push((format!("random-{i}"), e));
    }
    // encodings of random points
    for i in 0..30 {
        let s = Scalar::from_bytes_mod_order_wide(&rng.array::<64>());
        encodings.push((format!("point-{i}"), (RISTRETTO_BASEPOINT_TABLE * &s).compress().to_bytes()));
    }
    let mut decoded = 0;
    for (name, e) in &encodings {
        let d = CompressedRistretto(*e).decompress();
        let mut j = json!({"kind": "ristretto", "name": name, "bytes": hex(e), "valid": d.is_some()});
        if let Some(pt) = d {
            decoded += 1;
            assert_eq!(pt.compress().to_bytes(), *e);
            // twice the point, so that the Lean side checks arithmetic on the decoded representative
            j["double"] = Json::String(hex(&(pt + pt).compress().to_bytes()));
        }
        out.push("ristretto", j);
    }
    assert!(decoded > 50 && decoded < encodings.len() - 50);

    // base point multiples and double scalar multiples
    let mut scalars: Vec<(String, [u8; 32])> = vec![];
    let mut zero = [0u8; 32];
    scalars.push(("0".into(), zero));
    zero[0] = 1;
    scalars.push(("1".into(), zero));
    zero[0] = 2;
    scalars.push(("2".into(), zero));
    let mut ell_minus_1 = ELL;
    ell_minus_1[0] -= 1;
    scalars.push(("ell-1".into(), ell_minus_1));
    let mut top = [0u8; 32];
    top[31] = 0x0f;
    scalars.push(("2^252-1ish".into(), top));
    for i in 0..24 {
        scalars.push((format!("random-{i}"), Scalar::from_bytes_mod_order_wide(&rng.array::<64>()).to_bytes()));
    }
    for (name, s) in &scalars {
        let sc = canonical(s).unwrap();
        out.push(
            "basemul",
            json!({"kind": "basemul", "name": name, "scalar": hex(s), "point": hex(&(RISTRETTO_BASEPOINT_TABLE * &sc).compress().to_bytes())}),
        );
    }
    let valid_points: Vec<[u8; 32]> =
        encodings.iter().filter(|(_, e)| CompressedRistretto(*e).decompress().is_some()).map(|(_, e)| *e).collect();
    for i in 0..60 {
        let a = scalars[(i * 7) % scalars.len()].1;
        let b = scalars[(i * 11 + 3) % scalars.len()].1;
        let pa = valid_points[(i * 5) % valid_points.len()];
        let pb = valid_points[(i * 13 + 1) % valid_points.len()];
        let r = near_crypto_vmul2(&a, &pa, &b, &pb);
        out.push(
            "vmul2",
            json!({"kind": "vmul2", "name": format!("{i}"), "s1": hex(&a), "p1": hex(&pa), "s2": hex(&b), "p2": hex(&pb), "point": hex(&r)}),
        );
    }

    // ----- BLAKE2b-256 scalars the VRF hashes to -----
    // (covered by the hash vectors; the offsets appear in every compute line below)

    // ----- keys -----
    let mut seeds: Vec<(String, [u8; 32])> = vec![("zero".into(), [0; 32]), ("ff".into(), [0xff; 32])];
    let mut padded = [b' '; 32];
    padded[..4].copy_from_slice(b"test");
    seeds.push(("near-test-seed".into(), padded));
    for i in 0..14 {
        seeds.push((format!("random-{i}"), rng.array()));
    }
    let mut keys = vec![];
    for (name, seed) in &seeds {
        let (sk, kp) = vrf_secret(seed);
        let ed_pk = ED25519PublicKey(kp[32..].try_into().unwrap());
        let pk = sk.public_key();
        assert_eq!(convert_public_key(&ed_pk).unwrap(), *pk);
        out.push(
            "key",
            json!({"kind": "key", "name": name, "seed": hex(seed), "ed25519": hex(&kp[32..]),
                   "secret": hex(&bytes32(&sk)), "public": hex(&pk_bytes(pk))}),
        );
        keys.push((name.clone(), sk, kp));
    }

    // ----- conversion of ed25519 public keys -----
    let mut conv: Vec<(String, [u8; 32])> = vec![];
    for (name, _, kp) in &keys {
        conv.push((format!("{name}"), kp[32..].try_into().unwrap()));
        let mut flipped: [u8; 32] = kp[32..].try_into().unwrap();
        flipped[31] ^= 0x80;
        conv.push((format!("{name}/sign-flipped"), flipped));
    }
    // identity, small-order points, non-canonical y
    let mut id = [0u8; 32];
    id[0] = 1;
    conv.push(("identity".into(), id));
    for (i, t) in curve25519_dalek::constants::EIGHT_TORSION.iter().enumerate() {
        conv.push((format!("torsion-{i}"), t.compress().to_bytes()));
    }
    for k in 0..19u8 {
        let mut e = P_LE;
        e[0] = 0xed + k;
        conv.push((format!("y-p-plus-{k}"), e));
    }
    // mixed-order points: a + T
    for i in 1..8usize {
        let a = Scalar::from_bytes_mod_order_wide(&rng.array::<64>());
        let pt = curve25519_dalek::constants::ED25519_BASEPOINT_POINT * a + curve25519_dalek::constants::EIGHT_TORSION[i];
        conv.push((format!("mixed-{i}"), pt.compress().to_bytes()));
    }
    for i in 0..200 {
        conv.push((format!("random-{i}"), rng.array()));
    }
    let mut converted = 0;
    for (name, e) in &conv {
        let r = convert_public_key(&ED25519PublicKey(*e));
        let mut j = json!({"kind": "convert", "name": name, "ed25519": hex(e), "valid": r.is_some()});
        if let Some(pk) = r {
            converted += 1;
            j["public"] = Json::String(hex(&pk_bytes(&pk)));
        }
        out.push("convert", j);
    }
    assert!(converted > 15 && converted < conv.len() - 100);

    // ----- compute with proof -----
    let inputs: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("a".into(), b"a".to_vec()),
        ("32-ff".into(), vec![0xff; 32]),
        ("random-32".into(), rng.bytes(32)),
        ("random-33".into(), rng.bytes(33)),
        ("random-100".into(), rng.bytes(100)),
        ("random-200".into(), rng.bytes(200)),
    ];
    let mut computed: Vec<(String, [u8; 32], Vec<u8>, [u8; 32], [u8; 64])> = vec![];
    for (kn, sk, _) in &keys {
        for (i, (inn, input)) in inputs.iter().enumerate() {
            // every key with three inputs, the first keys with all
            if i % 3 != (kn.len() % 3) && !kn.starts_with("random-1") && !kn.starts_with("near") {
                continue;
            }
            let (value, proof) = sk.compute_vrf_with_proof(input);
            assert_eq!(sk.compute_vrf(input), value);
            assert!(sk.public_key().is_vrf_valid(input, &value, &proof));
            out.push(
                "compute",
                json!({"kind": "compute", "name": format!("{kn}/{inn}"), "secret": hex(&bytes32(sk)),
                       "public": hex(&pk_bytes(sk.public_key())), "input": hex(input),
                       "value": hex(&value.0), "proof": hex(&proof.0)}),
            );
            computed.push((format!("{kn}/{inn}"), pk_bytes(sk.public_key()), input.clone(), value.0, proof.0));
        }
    }
    // secret keys outside the seeds: small and near-order scalars
    for (name, s) in &scalars {
        let sk = SecretKey::try_from(s).unwrap();
        let input = rng.bytes(40);
        let (value, proof) = sk.compute_vrf_with_proof(&input);
        out.push(
            "compute",
            json!({"kind": "compute", "name": format!("scalar-{name}"), "secret": hex(s),
                   "public": hex(&pk_bytes(sk.public_key())), "input": hex(&input),
                   "value": hex(&value.0), "proof": hex(&proof.0)}),
        );
        computed.push((format!("scalar-{name}"), pk_bytes(sk.public_key()), input, value.0, proof.0));
    }

    // ----- public key decoding -----
    let mut pks: Vec<(String, [u8; 32])> = vec![];
    for (name, e) in &encodings {
        pks.push((name.clone(), *e));
    }
    for (name, e) in pks {
        let ok = PublicKey::try_from(&e).is_ok();
        out.push("vrf-public", json!({"kind": "vrf-public", "name": name, "bytes": hex(&e), "valid": ok}));
    }
    // ----- secret key decoding (canonical scalars only) -----
    let mut secrets: Vec<(String, [u8; 32])> = vec![];
    secrets.push(("ell".into(), ELL));
    let mut one_le = [0u8; 32];
    one_le[0] = 1;
    let (ell_plus_1, _) = add256(&ELL, &one_le);
    secrets.push(("ell+1".into(), ell_plus_1));
    secrets.push(("ff".into(), [0xff; 32]));
    secrets.push(("2^255".into(), {
        let mut b = [0u8; 32];
        b[31] = 0x80;
        b
    }));
    secrets.push(("ell-1".into(), ell_minus_1));
    for (name, s) in secrets {
        out.push("vrf-secret", json!({"kind": "vrf-secret", "name": name, "bytes": hex(&s), "valid": canonical(&s).is_some()}));
    }

    // ----- verification -----
    let (mut accepted, mut rejected) = (0, 0);
    let mut push_verify = |out: &mut Out, name: String, pk: &[u8; 32], input: &[u8], value: &[u8; 32], proof: &[u8; 64]| {
        let pkey = PublicKey::try_from(pk).expect("verification keys decode");
        let v = valid(&pkey, input, value, proof);
        if v {
            accepted += 1;
        } else {
            rejected += 1;
        }
        out.push(
            "verify",
            json!({"kind": "verify", "name": name, "public": hex(pk), "input": hex(input),
                   "value": hex(value), "proof": hex(proof), "valid": v}),
        );
        v
    };
    for (idx, (name, pk, input, value, proof)) in computed.iter().enumerate().take(24) {
        assert!(push_verify(out, format!("{name}/valid"), pk, input, value, proof));
        // wrong input
        let mut other = input.clone();
        if other.is_empty() { other.push(0) } else { other[0] ^= 1 }
        assert!(!push_verify(out, format!("{name}/wrong-input"), pk, &other, value, proof));
        let mut longer = input.clone();
        longer.push(0);
        assert!(!push_verify(out, format!("{name}/extended-input"), pk, &longer, value, proof));
        // wrong key
        let wrong = computed[(idx + 1) % computed.len()].1;
        if &wrong != pk {
            assert!(!push_verify(out, format!("{name}/other-key"), &wrong, input, value, proof));
        }
        // edits of the value
        for bit in [0usize, 1, 100, 254, 255] {
            let mut v = *value;
            set_bit(&mut v, bit);
            push_verify(out, format!("{name}/value-bit-{bit}"), pk, input, &v, proof);
        }
        // edits of the proof: r (bytes 0..32), c (bytes 32..64)
        for bit in [0usize, 1, 7, 100, 251, 252, 253, 254, 255, 256, 257, 300, 400, 508, 509, 510, 511] {
            let mut p = *proof;
            set_bit(&mut p, bit);
            push_verify(out, format!("{name}/proof-bit-{bit}"), pk, input, value, &p);
        }
        // r + ell, c + ell (same scalars, non-canonical), c = r, swapped halves, zero proof
        let r: [u8; 32] = proof[..32].try_into().unwrap();
        let c: [u8; 32] = proof[32..].try_into().unwrap();
        let (r_ell, carry) = add256(&r, &ELL);
        if !carry {
            let mut p = *proof;
            p[..32].copy_from_slice(&r_ell);
            assert!(!push_verify(out, format!("{name}/r-plus-ell"), pk, input, value, &p));
        }
        let (c_ell, carry) = add256(&c, &ELL);
        if !carry {
            let mut p = *proof;
            p[32..].copy_from_slice(&c_ell);
            assert!(!push_verify(out, format!("{name}/c-plus-ell"), pk, input, value, &p));
        }
        let mut swapped = [0u8; 64];
        swapped[..32].copy_from_slice(&c);
        swapped[32..].copy_from_slice(&r);
        push_verify(out, format!("{name}/halves-swapped"), pk, input, value, &swapped);
        push_verify(out, format!("{name}/zero-proof"), pk, input, value, &[0u8; 64]);
        let mut p = *proof;
        p[..32].copy_from_slice(&ELL);
        push_verify(out, format!("{name}/r-ell"), pk, input, value, &p);
        // the value replaced by other ristretto encodings
        let mut v = [0u8; 32];
        push_verify(out, format!("{name}/value-identity"), pk, input, &v, proof);
        v[0] = 1;
        push_verify(out, format!("{name}/value-odd"), pk, input, &v, proof);
        push_verify(out, format!("{name}/value-ff"), pk, input, &[0xff; 32], proof);
        push_verify(out, format!("{name}/value-base"), pk, input, &base_enc, proof);
        let mut v = P_LE;
        v[0] = 0xed;
        push_verify(out, format!("{name}/value-p"), pk, input, &v, proof);
    }
    assert!(accepted > 20 && rejected > 400, "{accepted} {rejected}");

    // ----- block randomness (`get_block_metadata`): the input is the previous random value and
    // the new one is the SHA-256 of the VRF value -----
    use near_primitives::validator_signer::InMemoryValidatorSigner;
    for (i, (name, _, kp)) in keys.iter().enumerate().take(10) {
        let signer = near_crypto::InMemorySigner::from_secret_key(
            "test.near".parse().unwrap(),
            near_crypto::SecretKey::ED25519(ED25519SecretKey(*kp)),
        );
        let prev: [u8; 32] = rng.array();
        let validator_signer = InMemoryValidatorSigner::from_signer(signer);
        let (value, proof) = validator_signer.compute_vrf_with_proof(&prev);
        let random = CryptoHash::hash_bytes(&value.0);
        let vrf_pk = convert_public_key(&ED25519PublicKey(kp[32..].try_into().unwrap())).unwrap();
        assert!(vrf_pk.is_vrf_valid(&prev.to_vec(), &value, &proof));
        out.push(
            "block",
            json!({"kind": "block", "name": format!("{name}-{i}"), "ed25519": hex(&kp[32..]), "prevRandom": hex(&prev),
                   "value": hex(&value.0), "proof": hex(&proof.0), "random": hex(random.as_ref())}),
        );
    }
}

fn near_crypto_vmul2(s1: &[u8; 32], p1: &[u8; 32], s2: &[u8; 32], p2: &[u8; 32]) -> [u8; 32] {
    let a = canonical(s1).unwrap();
    let b = canonical(s2).unwrap();
    let pa = CompressedRistretto(*p1).decompress().unwrap();
    let pb = CompressedRistretto(*p2).decompress().unwrap();
    curve25519_dalek::ristretto::RistrettoPoint::vartime_multiscalar_mul(&[a, b], [&pa, &pb]).compress().to_bytes()
}
