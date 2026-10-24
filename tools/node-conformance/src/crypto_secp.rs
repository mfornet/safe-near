//! secp256k1 fixtures: key derivation, signing, recovery, verification, public key parsing and
//! the VM's `ecrecover`, every verdict from the crates nearcore uses (`near-crypto` 0.37.4 and
//! `secp256k1` 0.27.0 over `libsecp256k1` of `secp256k1-sys` 0.8.2).

use super::{hex, Out, Rng};
use near_crypto::{KeyType, PublicKey, Secp256K1PublicKey, Secp256K1Signature, SecretKey, Signature};
use secp256k1::ecdsa::{RecoverableSignature, RecoveryId};
use secp256k1::{Message, PublicKey as SecpPublic, Secp256k1};
use serde_json::{json, Value};

const N: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc,
    0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41,
];
const P: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xfc, 0x2f,
];

type U = [u8; 32];

/// `a + b` as 256-bit big-endian integers, wrapping.
fn add(a: &U, b: &U) -> U {
    let mut out = [0u8; 32];
    let mut carry = 0u16;
    for i in (0..32).rev() {
        let s = a[i] as u16 + b[i] as u16 + carry;
        out[i] = s as u8;
        carry = s >> 8;
    }
    out
}

/// `a - b`, wrapping.
fn sub(a: &U, b: &U) -> U {
    let mut out = [0u8; 32];
    let mut borrow = 0i16;
    for i in (0..32).rev() {
        let mut d = a[i] as i16 - b[i] as i16 - borrow;
        borrow = 0;
        if d < 0 {
            d += 256;
            borrow = 1;
        }
        out[i] = d as u8;
    }
    out
}

fn small(v: u64) -> U {
    let mut b = [0u8; 32];
    b[24..].copy_from_slice(&v.to_be_bytes());
    b
}

fn shr1(a: &U) -> U {
    let mut out = [0u8; 32];
    let mut carry = 0u8;
    for i in 0..32 {
        out[i] = (a[i] >> 1) | carry;
        carry = a[i] << 7;
    }
    out
}

fn set_bit(b: &mut [u8], bit: usize) {
    // bit 0 is the least significant bit of the last byte (big-endian)
    let n = b.len();
    b[n - 1 - bit / 8] ^= 1 << (bit % 8);
}

/// The values at which scalars and field elements change behaviour.
fn edges() -> Vec<(&'static str, U)> {
    let one = small(1);
    let n_half = shr1(&sub(&N, &one)); // (n - 1) / 2
    let p_minus_n = sub(&P, &N);
    vec![
        ("0", small(0)),
        ("1", one),
        ("2", small(2)),
        ("n/2", n_half),
        ("n/2+1", add(&n_half, &one)),
        ("n-1", sub(&N, &one)),
        ("n", N),
        ("n+1", add(&N, &one)),
        ("p-n-1", sub(&p_minus_n, &one)),
        ("p-n", p_minus_n),
        ("p-n+1", add(&p_minus_n, &one)),
        ("p-1", sub(&P, &one)),
        ("p", P),
        ("p+1", add(&P, &one)),
        ("2^256-1", [0xff; 32]),
        ("2^255", {
            let mut b = [0u8; 32];
            b[0] = 0x80;
            b
        }),
    ]
}

fn ctx() -> Secp256k1<secp256k1::All> {
    Secp256k1::new()
}

/// `Signature::verify` of near-crypto: key (64 bytes), message and signature as bytes.
fn near_verify(pk: &[u8; 64], msg: &[u8], sig: &[u8; 65]) -> bool {
    let signature = Signature::from_parts(KeyType::SECP256K1, sig).unwrap();
    let key = PublicKey::SECP256K1(Secp256K1PublicKey::try_from(&pk[..]).unwrap());
    signature.verify(msg, &key)
}

/// `Secp256K1Signature::recover` as `ecrecover` calls it: the VM's body for well-formed arguments
/// (`near-vm-runner` 0.37.4, `logic.rs`, `ecrecover`): `check_signature_values`, then `recover`.
fn vm_ecrecover(hash: &[u8; 32], sig: &[u8; 64], v: u8, malleability: bool) -> Option<[u8; 64]> {
    let mut bytes = [0u8; 65];
    bytes[..64].copy_from_slice(sig);
    bytes[64] = v;
    let signature = Secp256K1Signature::from(bytes);
    if !signature.check_signature_values(malleability) {
        return None;
    }
    signature.recover(*hash).ok().map(|k| <[u8; 64]>::try_from(k.as_ref() as &[u8]).unwrap())
}

/// The key `secp256k1` recovers from `r ‖ s` with id `v` (any `i32`), as 64 bytes.
fn lib_recover(ctx: &Secp256k1<secp256k1::All>, msg: &[u8; 32], rs: &[u8; 64], v: i32) -> Option<[u8; 64]> {
    let id = RecoveryId::from_i32(v).ok()?;
    let sig = RecoverableSignature::from_compact(rs, id).ok()?;
    let key = ctx.recover_ecdsa(&Message::from_slice(msg).unwrap(), &sig).ok()?;
    Some(key.serialize_uncompressed()[1..65].try_into().unwrap())
}

fn raw_public(sk: &SecretKey) -> [u8; 64] {
    match sk.public_key() {
        PublicKey::SECP256K1(k) => <[u8; 64]>::try_from(k.as_ref() as &[u8]).unwrap(),
        _ => unreachable!(),
    }
}

fn secret_bytes(sk: &SecretKey) -> [u8; 32] {
    match sk {
        SecretKey::SECP256K1(k) => k.secret_bytes(),
        _ => unreachable!(),
    }
}

fn near_sign(sk: &SecretKey, msg: &[u8; 32]) -> [u8; 65] {
    match sk.sign(msg) {
        Signature::SECP256K1(s) => <[u8; 65]>::from(s),
        _ => unreachable!(),
    }
}

pub fn secp256k1(out: &mut Out) {
    let ctx = ctx();
    let mut rng = Rng::new(0x5ec9256);
    let edges = edges();

    // ----- secret keys -----
    for (name, v) in &edges {
        let valid = secp256k1::SecretKey::from_slice(v).is_ok();
        out.push("secret", json!({"kind": "secret", "name": name, "secret": hex(v), "valid": valid}));
    }

    // ----- key derivation -----
    let mut secrets: Vec<(String, [u8; 32])> = vec![];
    for (name, v) in [
        ("one", small(1)),
        ("two", small(2)),
        ("three", small(3)),
        ("n-1", sub(&N, &small(1))),
        ("n-2", sub(&N, &small(2))),
        ("n/2", shr1(&sub(&N, &small(1)))),
        ("n/2+1", add(&shr1(&sub(&N, &small(1))), &small(1))),
        ("2^255", edges.iter().find(|(n, _)| *n == "2^255").unwrap().1),
        ("2^128", {
            let mut b = [0u8; 32];
            b[15] = 1;
            b
        }),
        ("deadbeef", small(0xdead_beef)),
    ] {
        secrets.push((name.to_string(), v));
    }
    // near-crypto's own seeded keys
    for seed in ["test", "alice.near", "bob.near", "validator", "x"] {
        let sk = SecretKey::from_seed(KeyType::SECP256K1, seed);
        secrets.push((format!("near-seed-{seed}"), secret_bytes(&sk)));
    }
    for i in 0..30 {
        loop {
            let b: [u8; 32] = rng.array();
            if secp256k1::SecretKey::from_slice(&b).is_ok() {
                secrets.push((format!("random-{i}"), b));
                break;
            }
        }
    }
    // keys whose public x or y has leading zeros, and both parities
    for (name, secret) in &secrets {
        let sk = SecretKey::SECP256K1(secp256k1::SecretKey::from_slice(secret).unwrap());
        let public = raw_public(&sk);
        let pk = SecpPublic::from_secret_key(&ctx, &secp256k1::SecretKey::from_slice(secret).unwrap());
        assert_eq!(pk.serialize_uncompressed()[1..], public);
        out.push(
            "keypair",
            json!({"kind": "keypair", "name": name, "secret": hex(secret), "public": hex(&public),
                   "compressed": hex(&pk.serialize())}),
        );
    }

    // ----- signing (deterministic) -----
    let msg_edges: Vec<(String, [u8; 32])> = edges.iter().map(|(n, v)| (format!("msg-{n}"), *v)).collect();
    let mut signed: Vec<(SecretKey, [u8; 32], [u8; 65])> = vec![];
    let mut seen_recid = [0usize; 4];
    for (i, (name, secret)) in secrets.iter().enumerate() {
        let sk = SecretKey::SECP256K1(secp256k1::SecretKey::from_slice(secret).unwrap());
        let public = raw_public(&sk);
        for j in 0..3 {
            let msg: [u8; 32] = if j == 0 { msg_edges[(i * 3 + j) % msg_edges.len()].1 } else { rng.array() };
            let sig = near_sign(&sk, &msg);
            assert!(near_verify(&public, &msg, &sig));
            seen_recid[sig[64] as usize] += 1;
            out.push(
                "sign",
                json!({"kind": "sign", "name": format!("{name}-{j}"), "secret": hex(secret), "public": hex(&public),
                       "msg": hex(&msg), "sig": hex(&sig)}),
            );
            signed.push((sk.clone(), msg, sig));
        }
    }
    assert!(seen_recid[0] > 0 && seen_recid[1] > 0, "both parities of R.y");
    // Signing with an edge message on every edge scalar of the message space, for a fixed key.
    let fixed = SecretKey::SECP256K1(secp256k1::SecretKey::from_slice(&small(0xc0ffee)).unwrap());
    for (name, msg) in &msg_edges {
        let sig = near_sign(&fixed, msg);
        out.push(
            "sign",
            json!({"kind": "sign", "name": format!("c0ffee-{name}"), "secret": hex(&small(0xc0ffee)),
                   "public": hex(&raw_public(&fixed)), "msg": hex(msg), "sig": hex(&sig)}),
        );
    }

    // ----- public key parsing -----
    let mut inputs: Vec<(String, Vec<u8>)> = vec![];
    for (name, secret) in secrets.iter().take(18) {
        let pk = SecpPublic::from_secret_key(&ctx, &secp256k1::SecretKey::from_slice(secret).unwrap());
        let unc = pk.serialize_uncompressed();
        let comp = pk.serialize();
        inputs.push((format!("{name}/uncompressed"), unc.to_vec()));
        inputs.push((format!("{name}/compressed"), comp.to_vec()));
        // hybrid forms (tag 06 / 07) with the parity of y, and with the other one
        let mut hy = unc;
        hy[0] = 6 + (unc[64] & 1);
        inputs.push((format!("{name}/hybrid"), hy.to_vec()));
        let mut hy = unc;
        hy[0] = 7 - (unc[64] & 1);
        inputs.push((format!("{name}/hybrid-wrong-parity"), hy.to_vec()));
        // other tags on both lengths
        for tag in [0u8, 1, 5, 8, 0x42, 0xff] {
            let mut t = comp;
            t[0] = tag;
            inputs.push((format!("{name}/compressed-tag-{tag:02x}"), t.to_vec()));
            let mut t = unc;
            t[0] = tag;
            inputs.push((format!("{name}/uncompressed-tag-{tag:02x}"), t.to_vec()));
        }
        // compressed with the opposite parity tag, and a flipped bit in x or y
        let mut t = comp;
        t[0] ^= 1;
        inputs.push((format!("{name}/compressed-other-parity"), t.to_vec()));
        for bit in [0usize, 1, 100, 254, 255] {
            let mut t = unc;
            set_bit(&mut t[1..33], bit);
            inputs.push((format!("{name}/x-bit-{bit}"), t.to_vec()));
            let mut t = unc;
            set_bit(&mut t[33..65], bit);
            inputs.push((format!("{name}/y-bit-{bit}"), t.to_vec()));
        }
        for len in [0usize, 1, 32, 34, 63, 64, 66] {
            let mut t = unc.to_vec();
            t.resize(len, 0x04);
            inputs.push((format!("{name}/length-{len}"), t));
        }
    }
    // field-element edges as x with every tag: x >= p must fail, small x depends on the curve
    for (en, v) in &edges {
        for tag in [2u8, 3] {
            let mut c = vec![tag];
            c.extend_from_slice(v);
            inputs.push((format!("x-{en}/tag-{tag}"), c));
        }
        let mut u = vec![4u8];
        u.extend_from_slice(v);
        u.extend_from_slice(&small(2));
        inputs.push((format!("xy-{en}-2"), u));
        let mut u = vec![4u8];
        u.extend_from_slice(&small(1));
        u.extend_from_slice(v);
        inputs.push((format!("xy-1-{en}"), u));
    }
    // x = 1 .. 40 with both tags: roughly half of them are abscissae
    for x in 1..40u64 {
        for tag in [2u8, 3] {
            let mut c = vec![tag];
            c.extend_from_slice(&small(x));
            inputs.push((format!("small-x-{x}/tag-{tag}"), c));
        }
    }
    // the point at infinity and the origin in the uncompressed form
    inputs.push(("origin".into(), {
        let mut u = vec![4u8];
        u.extend_from_slice(&[0u8; 64]);
        u
    }));
    for i in 0..60 {
        let c: [u8; 32] = rng.array();
        let mut v = vec![2 + (i % 2) as u8];
        v.extend_from_slice(&c);
        inputs.push((format!("random-compressed-{i}"), v));
        let mut u = vec![4u8];
        u.extend_from_slice(&rng.array::<64>());
        inputs.push((format!("random-uncompressed-{i}"), u));
    }
    let mut parsed_valid = 0;
    for (name, bytes) in &inputs {
        let r = SecpPublic::from_slice(bytes);
        let mut j = json!({"kind": "pubkey", "name": name, "bytes": hex(bytes), "valid": r.is_ok()});
        if let Ok(pk) = r {
            parsed_valid += 1;
            j["public"] = Value::String(hex(&pk.serialize_uncompressed()[1..]));
            j["compressed"] = Value::String(hex(&pk.serialize()));
        }
        out.push("pubkey", j);
    }
    assert!(parsed_valid > 100 && parsed_valid < inputs.len() - 100);

    // ----- recovery -----
    // Valid signatures: the four recovery ids come from small `r` (x = r or r + n, both on the
    // curve for roughly half of the values), the others from the signer.
    let mut recover_cases: Vec<(String, [u8; 32], [u8; 64], i32)> = vec![];
    for (i, (sk, msg, sig)) in signed.iter().enumerate().take(40) {
        let rs: [u8; 64] = sig[..64].try_into().unwrap();
        let v = sig[64] as i32;
        recover_cases.push((format!("signed-{i}"), *msg, rs, v));
        for other in 0..4 {
            if other != v {
                recover_cases.push((format!("signed-{i}/v{other}"), *msg, rs, other));
            }
        }
        // high s: n - s with the opposite parity of the recovery id
        let s: U = rs[32..].try_into().unwrap();
        let hs = sub(&N, &s);
        let mut hrs = rs;
        hrs[32..].copy_from_slice(&hs);
        recover_cases.push((format!("signed-{i}/high-s"), *msg, hrs, v ^ 1));
        recover_cases.push((format!("signed-{i}/high-s-same-v"), *msg, hrs, v));
        for v in [4, 5, 255, -1] {
            recover_cases.push((format!("signed-{i}/v{v}"), *msg, rs, v));
        }
        let mut wrong = *msg;
        wrong[31] ^= 1;
        recover_cases.push((format!("signed-{i}/wrong-message"), wrong, rs, v));
        let _ = sk;
    }
    // r and s over the edge values, with random messages
    for (rn, r) in &edges {
        for (sn, s) in &edges {
            let mut rs = [0u8; 64];
            rs[..32].copy_from_slice(r);
            rs[32..].copy_from_slice(s);
            let msg: [u8; 32] = rng.array();
            for v in 0..4 {
                recover_cases.push((format!("r={rn},s={sn}/v{v}"), msg, rs, v));
            }
        }
    }
    // small r with a random s: both abscissae r and r + n
    for r in 1..60u64 {
        let mut rs = [0u8; 64];
        rs[..32].copy_from_slice(&small(r));
        rs[32..].copy_from_slice(&rng.array::<32>());
        rs[32] &= 0x7f;
        let msg: [u8; 32] = rng.array();
        for v in 0..4 {
            recover_cases.push((format!("small-r-{r}/v{v}"), msg, rs, v));
        }
    }
    // r around p - n: r + n < p exactly below the boundary
    let p_minus_n = sub(&P, &N);
    for d in -2i64..=2 {
        let r = if d < 0 { sub(&p_minus_n, &small((-d) as u64)) } else { add(&p_minus_n, &small(d as u64)) };
        for k in 0..6u32 {
            let mut rs = [0u8; 64];
            rs[..32].copy_from_slice(&r);
            rs[32..].copy_from_slice(&small(1 + k as u64 * 977));
            let msg: [u8; 32] = rng.array();
            for v in 2..4 {
                recover_cases.push((format!("r=p-n{d:+}/s{k}/v{v}"), msg, rs, v));
            }
        }
    }
    // random r, s, message
    for i in 0..60 {
        let mut rs: [u8; 64] = rng.array();
        if i % 2 == 0 {
            rs[0] &= 0x7f;
            rs[32] &= 0x7f;
        }
        let msg: [u8; 32] = rng.array();
        recover_cases.push((format!("random-{i}"), msg, rs, (i % 4) as i32));
    }
    let mut counts = [0usize; 4];
    let mut valid_count = 0;
    for (name, msg, rs, v) in &recover_cases {
        let key = lib_recover(&ctx, msg, rs, *v);
        // near-crypto's `recover` agrees whenever it does not panic (ids 0 to 3)
        if (0..4).contains(v) {
            let mut b = [0u8; 65];
            b[..64].copy_from_slice(rs);
            b[64] = *v as u8;
            let near = Secp256K1Signature::from(b).recover(*msg).ok().map(|k| <[u8; 64]>::try_from(k.as_ref() as &[u8]).unwrap());
            assert_eq!(near, key, "{name}");
        }
        if key.is_some() {
            valid_count += 1;
            counts[*v as usize] += 1;
        }
        let mut j = json!({"kind": "recover", "name": name, "msg": hex(msg), "sig": hex(rs), "v": v, "valid": key.is_some()});
        if let Some(k) = key {
            j["public"] = Value::String(hex(&k));
        }
        out.push("recover", j);
    }
    assert!(counts.iter().all(|c| *c > 5), "every recovery id recovers keys: {counts:?}");
    assert!(valid_count > 100);

    // ----- verification (near-crypto `Signature::verify`) -----
    let mut vcases: Vec<(String, [u8; 64], Vec<u8>, Vec<u8>)> = vec![];
    for (i, (sk, msg, sig)) in signed.iter().enumerate().take(30) {
        let pk = raw_public(sk);
        let tag = format!("signed-{i}");
        vcases.push((format!("{tag}/valid"), pk, msg.to_vec(), sig.to_vec()));
        let mut m = msg.to_vec();
        m[0] ^= 0x80;
        vcases.push((format!("{tag}/wrong-message"), pk, m, sig.to_vec()));
        for len in [0usize, 1, 31, 33, 64] {
            let mut m = msg.to_vec();
            m.resize(len, 0);
            vcases.push((format!("{tag}/message-length-{len}"), pk, m, sig.to_vec()));
        }
        for v in 0..8u8 {
            let mut s = sig.to_vec();
            s[64] = v;
            vcases.push((format!("{tag}/v{v}"), pk, msg.to_vec(), s));
        }
        let mut s = sig.to_vec();
        s[64] = 255;
        vcases.push((format!("{tag}/v255"), pk, msg.to_vec(), s));
        // s -> n - s (high), with and without the id adjusted
        let sv: U = sig[32..64].try_into().unwrap();
        let mut hs = sig.to_vec();
        hs[32..64].copy_from_slice(&sub(&N, &sv));
        vcases.push((format!("{tag}/high-s"), pk, msg.to_vec(), hs.clone()));
        hs[64] ^= 1;
        vcases.push((format!("{tag}/high-s-flipped-v"), pk, msg.to_vec(), hs));
        // another signer's key
        let other = raw_public(&signed[(i + 1) % signed.len()].0);
        vcases.push((format!("{tag}/other-key"), other, msg.to_vec(), sig.to_vec()));
        // bits of r and s, and of the key
        for bit in [0usize, 1, 7, 100, 200, 254, 255] {
            let mut s = sig.to_vec();
            set_bit(&mut s[..32], bit);
            vcases.push((format!("{tag}/r-bit-{bit}"), pk, msg.to_vec(), s));
            let mut s = sig.to_vec();
            set_bit(&mut s[32..64], bit);
            vcases.push((format!("{tag}/s-bit-{bit}"), pk, msg.to_vec(), s));
        }
        for bit in [0usize, 1, 100, 255, 256, 300, 511] {
            let mut k = pk;
            let b = bit % 256;
            if bit < 256 {
                set_bit(&mut k[32..], b);
            } else {
                set_bit(&mut k[..32], b);
            }
            vcases.push((format!("{tag}/key-bit-{bit}"), k, msg.to_vec(), sig.to_vec()));
        }
        // r + n (when it fits), s + n
        let rv: U = sig[..32].try_into().unwrap();
        let mut rn = sig.to_vec();
        rn[..32].copy_from_slice(&add(&rv, &N));
        vcases.push((format!("{tag}/r-plus-n"), pk, msg.to_vec(), rn));
        let mut sn = sig.to_vec();
        sn[32..64].copy_from_slice(&add(&sv, &N));
        vcases.push((format!("{tag}/s-plus-n"), pk, msg.to_vec(), sn));
    }
    // r, s at the edges for a fixed key and message
    let (sk0, msg0, sig0) = &signed[3];
    let pk0 = raw_public(sk0);
    for (rn, r) in &edges {
        for (sn, s) in &edges {
            let mut sg = sig0.to_vec();
            sg[..32].copy_from_slice(r);
            sg[32..64].copy_from_slice(s);
            vcases.push((format!("r={rn},s={sn}"), pk0, msg0.to_vec(), sg));
        }
    }
    // keys that are not points
    for (name, bytes) in inputs.iter().filter(|(n, b)| b.len() == 65 && b[0] == 4 && n.contains("bit")).take(30) {
        let k: [u8; 64] = bytes[1..65].try_into().unwrap();
        vcases.push((format!("{name}/key"), k, msg0.to_vec(), sig0.to_vec()));
    }
    for (en, v) in &edges {
        let mut k = pk0;
        k[..32].copy_from_slice(v);
        vcases.push((format!("key-x-{en}"), k, msg0.to_vec(), sig0.to_vec()));
        let mut k = pk0;
        k[32..].copy_from_slice(v);
        vcases.push((format!("key-y-{en}"), k, msg0.to_vec(), sig0.to_vec()));
    }
    vcases.push(("key-zero".into(), [0u8; 64], msg0.to_vec(), sig0.to_vec()));
    let (mut accepted, mut rejected) = (0, 0);
    for (name, pk, msg, sig) in &vcases {
        let sg: [u8; 65] = sig.as_slice().try_into().unwrap();
        // the message may have any length; `verify` takes it as given
        let valid = near_verify(pk, msg, &sg);
        if valid {
            accepted += 1;
        } else {
            rejected += 1;
        }
        out.push(
            "verify",
            json!({"kind": "verify", "name": name, "public": hex(pk), "msg": hex(msg), "sig": hex(sig), "valid": valid}),
        );
    }
    assert!(accepted > 60 && rejected > 300, "{accepted} {rejected}");

    // ----- the ecrecover host function (well-formed arguments) -----
    let mut ecases: Vec<(String, [u8; 32], [u8; 64], u8)> = vec![];
    for (name, msg, rs, v) in recover_cases.iter() {
        if (0..4).contains(v) {
            ecases.push((name.clone(), *msg, *rs, *v as u8));
        }
    }
    let mut eaccepted = [[0usize; 2]; 2];
    let mut n_e = 0;
    for (idx, (name, msg, rs, v)) in ecases.iter().enumerate() {
        // every case that recovers a key under either flag, and a quarter of the others
        let recovers = vm_ecrecover(msg, rs, *v, false).is_some() || vm_ecrecover(msg, rs, *v, true).is_some();
        if !recovers && idx % 4 != 0 {
            continue;
        }
        for malleability in [false, true] {
            let key = vm_ecrecover(msg, rs, *v, malleability);
            eaccepted[malleability as usize][key.is_some() as usize] += 1;
            n_e += 1;
            let mut j = json!({"kind": "ecrecover", "name": name, "hash": hex(msg), "sig": hex(rs), "v": v,
                               "malleability": malleability as u8, "valid": key.is_some()});
            if let Some(k) = key {
                j["public"] = Value::String(hex(&k));
            }
            out.push("ecrecover", j);
        }
    }
    assert!(n_e > 400);
    assert!(eaccepted[0][1] > 100 && eaccepted[1][0] > 100 && eaccepted[1][1] > 50, "{eaccepted:?}");
}
