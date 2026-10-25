//! P-256 fixtures: `p256_verify` as `near-vm-runner` 0.37.4 runs it (`logic/logic.rs`: `Signature::from_slice`,
//! `VerifyingKey::from_sec1_bytes`, `verify_prehash(message, signature)` of `p256` 0.13.2 and `ecdsa`
//! 0.16.9). The message is the pre-hashed digest of any length: fewer than 16 bytes never verifies,
//! more than 32 are cut to the leftmost 32, fewer are left-padded.

use super::crypto_vm::Vm;
use super::{hex, Out, Rng};
use p256::ecdsa::signature::hazmat::PrehashSigner;
use p256::ecdsa::{Signature, SigningKey, VerifyingKey};
use p256::elliptic_curve::ops::Reduce;
use p256::elliptic_curve::sec1::ToEncodedPoint;
use p256::{ProjectivePoint, Scalar, U256};
use serde_json::json;

const N: &str = "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551";
const P: &str = "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff";

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn add_small(a: &[u8], k: u64) -> Vec<u8> {
    let mut out = a.to_vec();
    let mut carry = k as u128;
    for b in out.iter_mut().rev() {
        let v = *b as u128 + (carry & 0xff);
        carry >>= 8;
        *b = v as u8;
        carry += v >> 8;
    }
    out
}

fn sub_small(a: &[u8], k: u64) -> Vec<u8> {
    let mut out = a.to_vec();
    let mut borrow = k as i128;
    for b in out.iter_mut().rev() {
        let v = *b as i128 - (borrow & 0xff);
        borrow >>= 8;
        if v < 0 {
            *b = (v + 256) as u8;
            borrow += 1;
        } else {
            *b = v as u8;
        }
    }
    out
}

struct Ctx<'a> {
    out: &'a mut Out,
    vm: Vm,
}

impl Ctx<'_> {
    fn run(&mut self, name: &str, sig: &[u8], msg: &[u8], pk: &[u8]) {
        let r = self.vm.p256(sig, msg, pk);
        self.out.push(
            "verify",
            json!({"kind": "verify", "name": name, "sig": hex(sig), "msg": hex(msg), "pk": hex(pk),
                   "ok": r.is_some(), "result": r}),
        );
    }
}

fn scalar_of(b: &[u8]) -> Scalar {
    <Scalar as Reduce<U256>>::reduce_bytes(p256::FieldBytes::from_slice(b))
}

pub fn p256(out: &mut Out) {
    let mut rng = Rng::new(0x32);
    let mut c = Ctx { out, vm: Vm::new(true) };
    let n = unhex(N);
    let p = unhex(P);
    let mut keys = vec![];
    for _ in 0..4 {
        let mut sk = rng.array::<32>();
        sk[0] &= 0x7f;
        let key = SigningKey::from_slice(&sk).unwrap();
        let pk = VerifyingKey::from(&key).to_encoded_point(true).as_bytes().to_vec();
        keys.push((key, pk));
    }
    let sign = |key: &SigningKey, msg: &[u8]| -> Vec<u8> {
        let s: Signature = key.sign_prehash(msg).unwrap();
        s.to_bytes().to_vec()
    };
    // valid signatures over messages of every length class: the host feeds the message as the digest
    for len in [16usize, 17, 20, 24, 31, 32, 33, 34, 40, 48, 63, 64, 65, 100, 128, 200, 1000, 5000] {
        let (key, pk) = &keys[len % keys.len()];
        let msg = rng.bytes(len);
        let sig = sign(key, &msg);
        c.run(&format!("valid-len-{len}"), &sig, &msg, pk);
        // the part beyond 32 bytes is ignored
        if len > 32 {
            let mut m2 = msg.clone();
            m2[len - 1] ^= 0xff;
            c.run(&format!("valid-len-{len}-tail-changed"), &sig, &m2, pk);
            let mut m3 = msg.clone();
            m3[31] ^= 1;
            c.run(&format!("valid-len-{len}-byte31-changed"), &sig, &m3, pk);
            c.run(&format!("valid-len-{len}-cut-to-32"), &sig, &msg[..32], pk);
        }
        let mut m4 = msg.clone();
        m4[0] ^= 1;
        c.run(&format!("wrong-message-len-{len}"), &sig, &m4, pk);
        c.run(&format!("wrong-key-len-{len}"), &sig, &msg, &keys[(len + 1) % keys.len()].1);
        // the same digest left-padded to 32 bytes
        if len < 32 {
            let mut padded = vec![0u8; 32 - len];
            padded.extend(&msg);
            c.run(&format!("valid-len-{len}-left-padded"), &sig, &padded, pk);
        }
    }
    // short messages are never accepted, even when signed by the signer's own code path
    for len in [0usize, 1, 2, 8, 15] {
        let (key, pk) = &keys[0];
        let msg = rng.bytes(len);
        let sig = sign(key, &rng.bytes(32));
        c.run(&format!("short-message-{len}"), &sig, &msg, pk);
    }
    // signature forms
    let (key, pk) = &keys[0];
    let msg = rng.bytes(32);
    let sig = sign(key, &msg);
    let (r, s) = (sig[..32].to_vec(), sig[32..].to_vec());
    let neg_s = {
        // n - s
        let mut o = n.clone();
        let mut borrow = 0i16;
        for i in (0..32).rev() {
            let mut d = o[i] as i16 - s[i] as i16 - borrow;
            borrow = 0;
            if d < 0 {
                d += 256;
                borrow = 1;
            }
            o[i] = d as u8;
        }
        o
    };
    let join = |a: &[u8], b: &[u8]| [a, b].concat();
    c.run("valid", &sig, &msg, pk);
    c.run("high-s-or-low-s-flipped", &join(&r, &neg_s), &msg, pk);
    for (name, rr, ss) in [
        ("r-zero", vec![0u8; 32], s.clone()),
        ("s-zero", r.clone(), vec![0u8; 32]),
        ("both-zero", vec![0u8; 32], vec![0u8; 32]),
        ("r-n", n.clone(), s.clone()),
        ("s-n", r.clone(), n.clone()),
        ("r-n-1", sub_small(&n, 1), s.clone()),
        ("s-n-1", r.clone(), sub_small(&n, 1)),
        ("r-n+1", add_small(&n, 1), s.clone()),
        ("s-n+1", r.clone(), add_small(&n, 1)),
        ("r-ff", vec![0xff; 32], s.clone()),
        ("s-ff", r.clone(), vec![0xff; 32]),
        ("r-one", add_small(&vec![0; 32], 1), s.clone()),
        ("s-one", r.clone(), add_small(&vec![0; 32], 1)),
        ("r-s-swapped", s.clone(), r.clone()),
        ("r-p", p.clone(), s.clone()),
    ] {
        c.run(name, &join(&rr, &ss), &msg, pk);
    }
    for bit in [0usize, 7, 100, 255] {
        let mut sg = sig.clone();
        sg[bit / 8] ^= 1 << (bit % 8);
        c.run(&format!("flip-r-bit-{bit}"), &sg, &msg, pk);
        let mut sg = sig.clone();
        sg[32 + bit / 8] ^= 1 << (bit % 8);
        c.run(&format!("flip-s-bit-{bit}"), &sg, &msg, pk);
    }
    for len in [0usize, 1, 32, 63, 65, 96, 128] {
        let mut sg = sig.repeat(3);
        sg.truncate(len);
        while sg.len() < len {
            sg.push(1);
        }
        c.run(&format!("sig-length-{len}"), &sg, &msg, pk);
    }
    // public key forms
    let x = pk[1..].to_vec();
    let other_parity = {
        let mut o = pk.clone();
        o[0] ^= 1;
        o
    };
    let key_cases: Vec<(String, Vec<u8>)> = vec![
        ("other-parity".into(), other_parity),
        ("tag-00".into(), [vec![0u8], x.clone()].concat()),
        ("tag-01".into(), [vec![1u8], x.clone()].concat()),
        ("tag-04".into(), [vec![4u8], x.clone()].concat()),
        ("tag-05".into(), [vec![5u8], x.clone()].concat()),
        ("tag-06".into(), [vec![6u8], x.clone()].concat()),
        ("tag-07".into(), [vec![7u8], x.clone()].concat()),
        ("tag-ff".into(), [vec![0xffu8], x.clone()].concat()),
        ("x-p".into(), [vec![2u8], p.clone()].concat()),
        ("x-p+1".into(), [vec![2u8], add_small(&p, 1)].concat()),
        ("x-ff".into(), [vec![3u8], vec![0xff; 32]].concat()),
        ("x-zero-tag-2".into(), [vec![2u8], vec![0; 32]].concat()),
        ("x-zero-tag-3".into(), [vec![3u8], vec![0; 32]].concat()),
        ("x-one-tag-2".into(), [vec![2u8], add_small(&vec![0; 32], 1)].concat()),
        ("all-zero".into(), vec![0; 33]),
        ("all-ff".into(), vec![0xff; 33]),
    ];
    for (name, k) in &key_cases {
        c.run(&format!("key-{name}"), &sig, &msg, k);
    }
    // abscissas without a root (about half of all)
    for i in 0..40 {
        let mut kx = rng.bytes(33);
        kx[0] = 2 + (i % 2) as u8;
        let parses = VerifyingKey::from_sec1_bytes(&kx).is_ok();
        c.run(&format!("key-random-{i}-parses-{parses}"), &sig, &msg, &kx);
    }
    for len in [0usize, 1, 32, 34, 64, 65] {
        let mut kk = pk.repeat(3);
        kk.truncate(len);
        while kk.len() < len {
            kk.push(2);
        }
        c.run(&format!("key-length-{len}"), &sig, &msg, &kk);
    }
    // 65-byte uncompressed and 64-byte raw forms are lengths the host rejects
    let (_, ck) = &keys[1];
    let uncompressed = VerifyingKey::from_sec1_bytes(ck).unwrap().to_encoded_point(false).as_bytes().to_vec();
    c.run("key-uncompressed-65", &sig, &msg, &uncompressed);
    c.run("key-raw-64", &sig, &msg, &uncompressed[1..]);
    // u1 G + u2 Q = infinity: Q = d G with z + r d = 0 (mod n), for the 32-byte digest z
    for i in 0..3 {
        let z = scalar_of(&msg);
        let rr = scalar_of(&rng.bytes(32));
        let d = -(z * rr.invert().unwrap());
        let q = ProjectivePoint::GENERATOR * d;
        let qk = q.to_affine().to_encoded_point(true).as_bytes().to_vec();
        let sg = join(&rr.to_bytes(), &scalar_of(&rng.bytes(32)).to_bytes());
        c.run(&format!("infinity-sum-{i}"), &sg, &msg, &qk);
    }
    // the key is the generator and the nonce point is read from the table of small multiples
    for k in 1u64..=4 {
        let d = Scalar::from(k);
        let sk = SigningKey::from_bytes(&d.to_bytes()).unwrap();
        let qk = VerifyingKey::from(&sk).to_encoded_point(true).as_bytes().to_vec();
        let m = rng.bytes(32);
        c.run(&format!("small-secret-{k}"), &sign(&sk, &m), &m, &qk);
    }
    // order of the host's checks: a signature outside [1, n - 1] answers false before the key or
    // the message is looked at (no trap for a bad key length), a bad key length traps before the
    // message is looked at, and a key that does not parse answers false whatever the message
    let bad_sig = join(&vec![0u8; 32], &s);
    for len in [0usize, 32, 34] {
        c.run(&format!("bad-sig-value-key-length-{len}"), &bad_sig, &msg, &vec![2u8; len]);
    }
    c.run("bad-sig-value-short-message-bad-key-length", &bad_sig, &msg[..4], &pk[..32]);
    c.run("good-sig-short-message-bad-key-length", &sig, &msg[..4], &pk[..32]);
    c.run("good-sig-short-message-bad-key", &sig, &msg[..4], &key_cases[1].1);
    c.run("good-sig-empty-message-bad-key-length", &sig, &[], &pk[..1]);
    c.run("bad-sig-length-bad-key-length", &sig[..63], &msg, &pk[..32]);
    // r equals the abscissa reduced modulo n: the signature of a message whose digest is zero
    let zero_msg = vec![0u8; 32];
    c.run("zero-digest", &sign(&keys[2].0, &zero_msg), &zero_msg, &keys[2].1);
    let ff_msg = vec![0xffu8; 32];
    c.run("ff-digest", &sign(&keys[2].0, &ff_msg), &ff_msg, &keys[2].1);
    let n_msg = n.clone();
    c.run("digest-n", &sign(&keys[3].0, &n_msg), &n_msg, &keys[3].1);
    c.run("digest-n-as-zero", &sign(&keys[3].0, &zero_msg), &n_msg, &keys[3].1);
}
