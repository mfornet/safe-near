//! BLS12-381 fixtures: the nine `bls12381_*` host functions of `near-vm-runner` 0.37.4
//! (`logic/bls12381.rs`, over `blst` 0.3.11) with the NEP-488 fix (`bls12381_not_in_group_fix`)
//! off (protocol 86) and on (protocol 155). Points are built with `blst`; every verdict is the host
//! function's.

use super::crypto_vm::Vm;
use super::{hex, Out, Rng};
use blst::*;
use serde_json::{json, Value};

const P: &str = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
const R: &str = "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001";

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

/// Big-endian `a + k` over `a.len()` bytes (wrapping), and `a - k`.
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

/// A group of the curve: generator, arithmetic and the encodings, over the `blst` functions.
trait Grp {
    const SIZE: usize;
    const COMP: usize;
    type P: Copy + Default;
    type A: Copy + Default;
    fn generator() -> Self::P;
    fn mult(p: &Self::P, scalar: &[u8; 32]) -> Self::P;
    fn add(a: &Self::P, b: &Self::P) -> Self::P;
    fn neg(p: &Self::P) -> Self::P;
    fn affine(p: &Self::P) -> Self::A;
    fn serialize(a: &Self::A) -> Vec<u8>;
    fn compress(a: &Self::A) -> Vec<u8>;
    fn uncompress(bytes: &[u8]) -> Option<Self::A>;
    fn in_group(a: &Self::A) -> bool;
}

macro_rules! group {
    ($name:ident, $size:expr, $comp:expr, $p:ty, $a:ty, $base:ident, $mult:ident, $add:ident, $cneg:ident,
     $to_affine:ident, $ser:ident, $compress:ident, $uncompress:ident, $in_group:ident) => {
        struct $name;
        impl Grp for $name {
            const SIZE: usize = $size;
            const COMP: usize = $comp;
            type P = $p;
            type A = $a;
            fn generator() -> $p {
                unsafe { *$base() }
            }
            fn mult(p: &$p, scalar: &[u8; 32]) -> $p {
                let mut out = <$p>::default();
                unsafe { $mult(&mut out, p, scalar.as_ptr(), 256) };
                out
            }
            fn add(a: &$p, b: &$p) -> $p {
                let mut out = <$p>::default();
                unsafe { $add(&mut out, a, b) };
                out
            }
            fn neg(p: &$p) -> $p {
                let mut out = *p;
                unsafe { $cneg(&mut out, true) };
                out
            }
            fn affine(p: &$p) -> $a {
                let mut out = <$a>::default();
                unsafe { $to_affine(&mut out, p) };
                out
            }
            fn serialize(a: &$a) -> Vec<u8> {
                let mut out = vec![0u8; $size];
                unsafe { $ser(out.as_mut_ptr(), a) };
                out
            }
            fn compress(a: &$a) -> Vec<u8> {
                let mut out = vec![0u8; $comp];
                unsafe { $compress(out.as_mut_ptr(), a) };
                out
            }
            fn uncompress(bytes: &[u8]) -> Option<$a> {
                let mut out = <$a>::default();
                let e = unsafe { $uncompress(&mut out, bytes.as_ptr()) };
                // the (0, ±2) points of G1 are reported as not in the group but are decoded
                (e == BLST_ERROR::BLST_SUCCESS || e == BLST_ERROR::BLST_POINT_NOT_IN_GROUP).then_some(out)
            }
            fn in_group(a: &$a) -> bool {
                unsafe { $in_group(a) }
            }
        }
    };
}

group!(G1, 96, 48, blst_p1, blst_p1_affine, blst_p1_generator, blst_p1_mult, blst_p1_add_or_double, blst_p1_cneg,
       blst_p1_to_affine, blst_p1_affine_serialize, blst_p1_affine_compress, blst_p1_uncompress, blst_p1_affine_in_g1);
group!(G2, 192, 96, blst_p2, blst_p2_affine, blst_p2_generator, blst_p2_mult, blst_p2_add_or_double, blst_p2_cneg,
       blst_p2_to_affine, blst_p2_affine_serialize, blst_p2_affine_compress, blst_p2_uncompress, blst_p2_affine_in_g2);

/// A point of `G` as its uncompressed bytes, from its bytes `[k]G`.
fn point<G: Grp>(scalar: &[u8; 32]) -> G::P {
    G::mult(&G::generator(), scalar)
}

fn bytes<G: Grp>(p: &G::P) -> Vec<u8> {
    G::serialize(&G::affine(p))
}

fn comp<G: Grp>(p: &G::P) -> Vec<u8> {
    G::compress(&G::affine(p))
}

fn rand_scalar(rng: &mut Rng) -> [u8; 32] {
    let mut s: [u8; 32] = rng.array();
    s[31] &= 0x3f; // below r (about 2^254.9) up to a negligible set; the bound is not needed
    s
}

/// A point of the curve that is (with overwhelming probability) outside the prime-order group:
/// a random abscissa with a root.
fn off_group<G: Grp>(rng: &mut Rng) -> (G::A, Vec<u8>) {
    loop {
        let mut x = rng.bytes(G::COMP);
        x[0] = (x[0] & 0x1f) | 0x80;
        if let Some(a) = G::uncompress(&x) {
            if !G::in_group(&a) {
                let s = G::serialize(&a);
                return (a, s);
            }
        }
    }
}

struct Ctx<'a> {
    out: &'a mut Out,
    v0: Vm,
    v1: Vm,
}

fn reply(r: Option<super::crypto_vm::Reply>) -> Value {
    match r {
        None => json!({"trap": true}),
        Some(r) if r.ret == 0 && !r.out.is_empty() => json!({"ret": r.ret, "output": hex(&r.out)}),
        Some(r) => json!({"ret": r.ret}),
    }
}

impl Ctx<'_> {
    fn run(&mut self, func: &str, name: &str, input: &[u8]) {
        let (a, b) = (self.v0.bls(func, input), self.v1.bls(func, input));
        self.out.push(
            func,
            json!({"kind": func, "name": name, "input": hex(input), "v0": reply(a), "v1": reply(b)}),
        );
    }
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

/// A random canonical field element (48 big-endian bytes below `p`).
fn rand_fp(rng: &mut Rng, p: &[u8]) -> Vec<u8> {
    loop {
        let mut x = rng.bytes(48);
        x[0] &= 0x1f;
        if x.as_slice() < p {
            return x;
        }
    }
}

fn flag(b: &[u8], mask: u8) -> Vec<u8> {
    let mut o = b.to_vec();
    o[0] |= mask;
    o
}

fn run_group<G: Grp>(c: &mut Ctx, rng: &mut Rng, g: &str) {
    let s = G::SIZE;
    let cs = G::COMP;
    let base = G::generator();
    let (func_sum, func_mul, func_dec) = (format!("{g}_sum"), format!("{}_multiexp", g.replace('p', "g")), format!("{g}_decompress"));
    let (func_sum, func_mul, func_dec) = (func_sum.as_str(), func_mul.as_str(), func_dec.as_str());
    let inf = G::serialize(&G::A::default());
    let inf_c = G::compress(&G::A::default());
    assert_eq!(inf[0], 0x40);
    let one = {
        let mut o = [0u8; 32];
        o[0] = 1;
        o
    };
    let small = |k: u8| {
        let mut o = [0u8; 32];
        o[0] = k;
        o
    };
    let rand_pt = |rng: &mut Rng| point::<G>(&rand_scalar(rng));
    let sgn = |n: u8, p: &[u8]| cat(&[&[n], p]);
    let (_, off_bytes) = off_group::<G>(rng);
    let off2 = off_group::<G>(rng).1;
    let p = rand_pt(rng);
    let q = rand_pt(rng);
    let pb = bytes::<G>(&p);
    let qb = bytes::<G>(&q);
    let gb = bytes::<G>(&base);

    // The points of order 3 with abscissa zero: (0, ±2) on E1 (y² = x³ + 4); on E2 the abscissa 0
    // gives y² = 4 (1 + u). Built through the compressed form, whatever blst says.
    let mut corner: Vec<(String, Vec<u8>)> = vec![];
    for sign in [0u8, 0x20] {
        let mut x = vec![0u8; cs];
        x[0] = 0x80 | sign;
        if let Some(a) = G::uncompress(&x) {
            corner.push((format!("x0-sign{sign}"), G::serialize(&a)));
        }
    }

    // ---- sum
    c.run(func_sum, "empty", &[]);
    for neg in [0u8, 1] {
        c.run(func_sum, &format!("generator-{neg}"), &sgn(neg, &gb));
        c.run(func_sum, &format!("random-{neg}"), &sgn(neg, &pb));
        c.run(func_sum, &format!("infinity-{neg}"), &sgn(neg, &inf));
        c.run(func_sum, &format!("off-group-{neg}"), &sgn(neg, &off_bytes));
    }
    c.run(func_sum, "p-minus-p", &cat(&[&sgn(0, &pb), &sgn(1, &pb)]));
    c.run(func_sum, "p-plus-neg-p", &cat(&[&sgn(0, &pb), &sgn(0, &bytes::<G>(&G::neg(&p)))]));
    c.run(func_sum, "p-plus-p", &cat(&[&sgn(0, &pb), &sgn(0, &pb)]));
    c.run(func_sum, "p-minus-neg-p", &cat(&[&sgn(0, &pb), &sgn(1, &bytes::<G>(&G::neg(&p)))]));
    c.run(func_sum, "neg-p-neg-p", &cat(&[&sgn(1, &pb), &sgn(1, &pb)]));
    c.run(func_sum, "p-plus-inf", &cat(&[&sgn(0, &pb), &sgn(0, &inf)]));
    c.run(func_sum, "inf-minus-p", &cat(&[&sgn(1, &inf), &sgn(1, &pb)]));
    c.run(func_sum, "inf-x3", &cat(&[&sgn(0, &inf), &sgn(1, &inf), &sgn(0, &inf)]));
    c.run(func_sum, "p-q-minus-p-q", &cat(&[&sgn(0, &pb), &sgn(0, &qb), &sgn(1, &pb), &sgn(1, &qb)]));
    let pq = G::add(&p, &q);
    c.run(func_sum, "p-plus-q-minus-sum", &cat(&[&sgn(0, &pb), &sgn(0, &qb), &sgn(1, &bytes::<G>(&pq))]));
    c.run(func_sum, "off-group-pair", &cat(&[&sgn(0, &off_bytes), &sgn(0, &off2)]));
    c.run(func_sum, "off-group-doubled", &cat(&[&sgn(0, &off_bytes), &sgn(0, &off_bytes)]));
    c.run(func_sum, "off-group-cancel", &cat(&[&sgn(0, &off_bytes), &sgn(1, &off_bytes)]));
    c.run(func_sum, "off-group-and-group", &cat(&[&sgn(0, &off_bytes), &sgn(0, &pb)]));
    for (name, cb) in &corner {
        c.run(func_sum, &format!("corner-{name}"), &sgn(0, cb));
        c.run(func_sum, &format!("corner-{name}-neg"), &sgn(1, cb));
        c.run(func_sum, &format!("corner-{name}-twice"), &cat(&[&sgn(0, cb), &sgn(0, cb)]));
        c.run(func_sum, &format!("corner-{name}-with-p"), &cat(&[&sgn(0, &pb), &sgn(0, cb)]));
    }
    for n in (2..=10).chain([16, 33]) {
        let mut data = vec![];
        for _ in 0..n {
            let neg = rng.array::<1>()[0] & 1;
            data.extend(sgn(neg, &bytes::<G>(&rand_pt(rng))));
        }
        c.run(func_sum, &format!("random-{n}"), &data);
    }
    for sign in [2u8, 3, 0x80, 0xff] {
        c.run(func_sum, &format!("bad-sign-{sign}"), &sgn(sign, &pb));
        c.run(func_sum, &format!("bad-sign-{sign}-after-good"), &cat(&[&sgn(0, &pb), &sgn(sign, &qb)]));
    }
    c.run(func_sum, "bad-sign-and-bad-point", &sgn(2, &vec![0xff; s]));
    for len in [1, 2, s - 1, s, s + 2, 2 * s, 2 * s + 1, 2 * s + 3] {
        let mut d = sgn(0, &pb).repeat(3);
        d.truncate(len);
        while d.len() < len {
            d.push(5);
        }
        c.run(func_sum, &format!("length-{len}"), &d);
    }

    // ---- invalid encodings, shared by every function that takes an uncompressed point
    let mut bad: Vec<(String, Vec<u8>)> = vec![
        ("flag-compressed".into(), flag(&pb, 0x80)),
        ("flag-sort".into(), flag(&pb, 0x20)),
        ("flag-infinity".into(), flag(&pb, 0x40)),
        ("flag-infinity-sort".into(), flag(&inf, 0x20)),
        ("flag-infinity-compressed".into(), flag(&inf, 0x80)),
        ("flag-all-on-inf".into(), flag(&inf, 0xe0)),
        ("infinity-trailing-byte".into(), {
            let mut o = inf.clone();
            o[s - 1] = 1;
            o
        }),
        ("infinity-middle-byte".into(), {
            let mut o = inf.clone();
            o[s / 2] = 1;
            o
        }),
        ("all-zero".into(), vec![0; s]),
        ("all-ff".into(), vec![0xff; s]),
        ("all-one".into(), {
            let mut o = vec![0; s];
            o[s - 1] = 1;
            o
        }),
        ("y-flipped".into(), {
            let mut o = pb.clone();
            o[s - 1] ^= 1;
            o
        }),
        ("x-flipped".into(), {
            let mut o = pb.clone();
            o[s / 2 - 1] ^= 1;
            o
        }),
        ("swapped-halves".into(), cat(&[&pb[s / 2..], &pb[..s / 2]])),
        ("top-bits-of-x-set-0x40-with-point".into(), flag(&gb, 0x40)),
    ];
    let p48 = unhex(P);
    // coordinates (the 48-byte words) equal to p, p + 1, p + the coordinate, 2^384 - 1
    for k in 0..s / 48 {
        for (name, v) in [("p", p48.clone()), ("p+1", add_small(&p48, 1)), ("ff", vec![0xff; 48]), ("p+x", {
            let w = &pb[k * 48..k * 48 + 48];
            let mut o = w.to_vec();
            let mut carry = 0u16;
            for i in (0..48).rev() {
                let t = o[i] as u16 + p48[i] as u16 + carry;
                o[i] = t as u8;
                carry = t >> 8;
            }
            o
        })] {
            let mut o = pb.clone();
            o[k * 48..k * 48 + 48].copy_from_slice(&v);
            bad.push((format!("word{k}-{name}"), o));
        }
    }
    for (n, b) in &corner {
        bad.push((format!("corner-{n}-flipped"), {
            let mut o = b.clone();
            o[s - 1] ^= 2;
            o
        }));
    }
    for (name, b) in &bad {
        c.run(func_sum, &format!("bad-{name}"), &sgn(0, b));
        c.run(func_sum, &format!("bad-{name}-middle"), &cat(&[&sgn(0, &pb), &sgn(1, b), &sgn(0, &qb)]));
    }

    // ---- multiexp
    let m = |pt: &[u8], sc: &[u8]| cat(&[pt, sc]);
    let rr = unhex(R);
    let mut r_le = rr.clone();
    r_le.reverse();
    let r_le: [u8; 32] = r_le.try_into().unwrap();
    let r_minus_1 = {
        let mut o = r_le;
        o[0] -= 1;
        o
    };
    let r_plus_1 = {
        let mut o = r_le;
        o[0] += 1;
        o
    };
    c.run(func_mul, "empty", &[]);
    for (name, sc) in [
        ("0", [0u8; 32]),
        ("1", one),
        ("2", small(2)),
        ("3", small(3)),
        ("255", small(255)),
        ("r-1", r_minus_1),
        ("r", r_le),
        ("r+1", r_plus_1),
        ("2^256-1", [0xff; 32]),
        ("2^255", {
            let mut o = [0u8; 32];
            o[31] = 0x80;
            o
        }),
        ("2^64", {
            let mut o = [0u8; 32];
            o[8] = 1;
            o
        }),
        ("random", rng.array()),
        ("random-2", rng.array()),
    ] {
        c.run(func_mul, &format!("generator-times-{name}"), &m(&gb, &sc));
        c.run(func_mul, &format!("random-times-{name}"), &m(&pb, &sc));
    }
    c.run(func_mul, "infinity", &m(&inf, &rng.array::<32>()));
    c.run(func_mul, "infinity-zero-scalar", &m(&inf, &[0; 32]));
    c.run(func_mul, "infinity-and-point", &cat(&[&m(&inf, &small(7)), &m(&pb, &small(9))]));
    c.run(func_mul, "off-group", &m(&off_bytes, &one));
    c.run(func_mul, "off-group-zero-scalar", &m(&off_bytes, &[0; 32]));
    c.run(func_mul, "off-group-after-good", &cat(&[&m(&pb, &one), &m(&off_bytes, &one)]));
    c.run(func_mul, "off-group-before-good", &cat(&[&m(&off_bytes, &one), &m(&pb, &one)]));
    for (name, cb) in &corner {
        c.run(func_mul, &format!("corner-{name}"), &m(cb, &one));
        c.run(func_mul, &format!("corner-{name}-zero"), &m(cb, &[0; 32]));
    }
    c.run(func_mul, "same-point-twice", &cat(&[&m(&pb, &small(5)), &m(&pb, &small(6))]));
    c.run(func_mul, "point-and-negation", &cat(&[&m(&pb, &small(5)), &m(&bytes::<G>(&G::neg(&p)), &small(5))]));
    c.run(func_mul, "point-and-negation-diff", &cat(&[&m(&pb, &small(6)), &m(&bytes::<G>(&G::neg(&p)), &small(5))]));
    for n in (1..=10).chain([16, 17, 33]) {
        let mut data = vec![];
        for _ in 0..n {
            data.extend(m(&bytes::<G>(&rand_pt(rng)), &rng.array::<32>()));
        }
        c.run(func_mul, &format!("random-{n}"), &data);
    }
    let mut data = vec![];
    for _ in 0..8 {
        data.extend(m(&bytes::<G>(&rand_pt(rng)), &r_minus_1));
    }
    c.run(func_mul, "eight-scalars-r-1", &data);
    for len in [1, s - 1, s, s + 1, s + 31, s + 32 + 1, 2 * (s + 32) - 1] {
        let mut d = m(&pb, &one).repeat(3);
        d.truncate(len);
        while d.len() < len {
            d.push(5);
        }
        c.run(func_mul, &format!("length-{len}"), &d);
    }
    for (name, b) in &bad {
        c.run(func_mul, &format!("bad-{name}"), &m(b, &one));
        c.run(func_mul, &format!("bad-{name}-zero-scalar"), &m(b, &[0; 32]));
    }

    // ---- decompress
    c.run(func_dec, "empty", &[]);
    let kinds = |p: &G::P| comp::<G>(p);
    let cp = kinds(&p);
    let cq = kinds(&q);
    c.run(func_dec, "generator", &kinds(&base));
    c.run(func_dec, "random", &cp);
    c.run(func_dec, "random-neg", &kinds(&G::neg(&p)));
    c.run(func_dec, "infinity", &inf_c);
    c.run(func_dec, "off-group", &G::compress(&off_group::<G>(rng).0));
    c.run(func_dec, "off-group-neg", &{
        let a = off_group::<G>(rng).0;
        let c0 = G::compress(&a);
        flag(&c0, 0).iter().enumerate().map(|(i, b)| if i == 0 { b ^ 0x20 } else { *b }).collect::<Vec<u8>>()
    });
    for n in [2usize, 3, 5, 9] {
        let mut data = vec![];
        for _ in 0..n {
            data.extend(kinds(&rand_pt(rng)));
        }
        c.run(func_dec, &format!("random-{n}"), &data);
    }
    c.run(func_dec, "mixed", &cat(&[&cp, &inf_c, &cq]));
    for (name, b) in [
        ("flip-sort", { let mut o = cp.clone(); o[0] ^= 0x20; o }),
        ("clear-compressed", { let mut o = cp.clone(); o[0] &= 0x7f; o }),
        ("uncompressed-form-prefix", { let mut o = cp.clone(); o[0] &= 0x1f; o }),
        ("infinity-flag-with-data", flag(&cp, 0x40)),
        ("infinity-sort", flag(&inf_c, 0x20)),
        ("infinity-no-compressed", { let mut o = inf_c.clone(); o[0] = 0x40; o }),
        ("infinity-trailing", { let mut o = inf_c.clone(); o[cs - 1] = 1; o }),
        ("infinity-middle", { let mut o = inf_c.clone(); o[cs / 2] = 0x10; o }),
        ("all-ff", vec![0xff; cs]),
        ("all-80", { let mut o = vec![0; cs]; o[0] = 0x80; o }),
        ("x-is-p", { let mut o = if cs == 48 { p48.clone() } else { cat(&[&p48, &p48]) }; o[0] |= 0x80; o }),
        ("x-is-p-minus-1", { let mut o = if cs == 48 { sub_small(&p48, 1) } else { cat(&[&sub_small(&p48, 1), &sub_small(&p48, 1)]) }; o[0] |= 0x80; o }),
        ("x-is-one", { let mut o = vec![0; cs]; o[cs - 1] = 1; o[0] |= 0x80; o }),
        ("x-is-one-sort", { let mut o = vec![0; cs]; o[cs - 1] = 1; o[0] |= 0xa0; o }),
    ] {
        c.run(func_dec, &format!("bad-{name}"), &b);
        c.run(func_dec, &format!("bad-{name}-after-good"), &cat(&[&cp, &b]));
    }
    // x = 0 (the corner points of E1), and abscissas without a root
    for sign in [0x80u8, 0xa0] {
        let mut x = vec![0u8; cs];
        x[0] = sign;
        c.run(func_dec, &format!("x0-{sign:#x}"), &x);
    }
    let mut tries = 0;
    while tries < 40 {
        tries += 1;
        let mut x = rng.bytes(cs);
        x[0] = (x[0] & 0x1f) | 0x80 | if tries % 2 == 0 { 0x20 } else { 0 };
        let has = G::uncompress(&x).is_some();
        c.run(func_dec, &format!("random-abscissa-{tries}-root-{has}"), &x);
    }
    for len in [1, cs - 1, cs + 1, 2 * cs - 1, 2 * cs + 5] {
        let mut d = cp.repeat(3);
        d.truncate(len);
        while d.len() < len {
            d.push(0x81);
        }
        c.run(func_dec, &format!("length-{len}"), &d);
    }
    // uncompressed bytes given to decompress
    c.run(func_dec, "uncompressed-form", &pb[..cs]);
}

pub fn bls12381(out: &mut Out) {
    let mut rng = Rng::new(0x31);
    let mut c = Ctx { out, v0: Vm::new(false), v1: Vm::new(true) };
    let p = unhex(P);
    run_group::<G1>(&mut c, &mut rng, "p1");
    run_group::<G2>(&mut c, &mut rng, "p2");

    // ---- map_fp_to_g1 and map_fp2_to_g2
    let one = {
        let mut o = vec![0u8; 48];
        o[47] = 1;
        o
    };
    let fp_cases: Vec<(String, Vec<u8>)> = vec![
        ("zero".into(), vec![0; 48]),
        ("one".into(), one.clone()),
        ("two".into(), add_small(&one, 1)),
        ("p-1".into(), sub_small(&p, 1)),
        ("p-2".into(), sub_small(&p, 2)),
        ("(p-1)/2".into(), {
            let mut o = sub_small(&p, 1);
            let mut carry = 0u8;
            for b in o.iter_mut() {
                let n = (*b >> 1) | (carry << 7);
                carry = *b & 1;
                *b = n;
            }
            o
        }),
        ("11".into(), add_small(&vec![0; 48], 11)),
        ("p".into(), p.clone()),
        ("p+1".into(), add_small(&p, 1)),
        ("2^384-1".into(), vec![0xff; 48]),
        ("2^381".into(), { let mut o = vec![0; 48]; o[0] = 0x20; o }),
        ("2^381-1".into(), { let mut o = vec![0xff; 48]; o[0] = 0x1f; o }),
    ];
    for (name, b) in &fp_cases {
        c.run("map_fp_to_g1", name, b);
    }
    let rand_fp1: Vec<Vec<u8>> = (0..24).map(|_| rand_fp(&mut rng, &p)).collect();
    for (i, b) in rand_fp1.iter().enumerate() {
        c.run("map_fp_to_g1", &format!("random-{i}"), b);
    }
    c.run("map_fp_to_g1", "empty", &[]);
    for n in [2usize, 3, 8] {
        c.run("map_fp_to_g1", &format!("many-{n}"), &rand_fp1[..n].concat());
    }
    c.run("map_fp_to_g1", "bad-in-middle", &cat(&[&rand_fp1[0], &p, &rand_fp1[1]]));
    c.run("map_fp_to_g1", "bad-last", &cat(&[&rand_fp1[0], &rand_fp1[1], &vec![0xff; 48]]));
    for len in [1, 47, 49, 95, 97, 143] {
        let mut d = rand_fp1.concat();
        d.truncate(len);
        c.run("map_fp_to_g1", &format!("length-{len}"), &d);
    }
    // Fp2 inputs are c1 || c0
    let mut fp2_cases: Vec<(String, Vec<u8>)> = vec![];
    for (n1, b1) in fp_cases.iter().take(7) {
        for (n0, b0) in fp_cases.iter().take(7) {
            fp2_cases.push((format!("c1-{n1}-c0-{n0}"), cat(&[b1, b0])));
        }
    }
    for (n, b) in fp_cases.iter().skip(7) {
        fp2_cases.push((format!("c1-{n}-c0-random"), cat(&[b, &rand_fp1[0]])));
        fp2_cases.push((format!("c1-random-c0-{n}"), cat(&[&rand_fp1[1], b])));
    }
    for (name, b) in &fp2_cases {
        c.run("map_fp2_to_g2", name, b);
    }
    let rand_fp2: Vec<Vec<u8>> = (0..24).map(|_| cat(&[&rand_fp(&mut rng, &p), &rand_fp(&mut rng, &p)])).collect();
    for (i, b) in rand_fp2.iter().enumerate() {
        c.run("map_fp2_to_g2", &format!("random-{i}"), b);
    }
    c.run("map_fp2_to_g2", "empty", &[]);
    for n in [2usize, 3, 8] {
        c.run("map_fp2_to_g2", &format!("many-{n}"), &rand_fp2[..n].concat());
    }
    c.run("map_fp2_to_g2", "bad-in-middle", &cat(&[&rand_fp2[0], &cat(&[&p, &rand_fp1[0]]), &rand_fp2[1]]));
    for len in [1, 47, 95, 97, 143, 191, 193] {
        let mut d = rand_fp2.concat();
        d.truncate(len);
        c.run("map_fp2_to_g2", &format!("length-{len}"), &d);
    }

    // ---- pairing_check
    let g1g = G1::generator();
    let g2g = G2::generator();
    let pair = |a: &blst_p1, b: &blst_p2| cat(&[&bytes::<G1>(a), &bytes::<G2>(b)]);
    let inf1 = G1::serialize(&blst_p1_affine::default());
    let inf2 = G2::serialize(&blst_p2_affine::default());
    c.run("pairing_check", "empty", &[]);
    c.run("pairing_check", "inf-inf", &cat(&[&inf1, &inf2]));
    c.run("pairing_check", "generator-inf", &cat(&[&bytes::<G1>(&g1g), &inf2]));
    c.run("pairing_check", "inf-generator", &cat(&[&inf1, &bytes::<G2>(&g2g)]));
    c.run("pairing_check", "generators", &pair(&g1g, &g2g));
    c.run("pairing_check", "generators-negated", &cat(&[&pair(&g1g, &g2g), &pair(&G1::neg(&g1g), &g2g)]));
    c.run("pairing_check", "generators-negated-g2", &cat(&[&pair(&g1g, &g2g), &pair(&g1g, &G2::neg(&g2g))]));
    c.run("pairing_check", "generators-twice", &cat(&[&pair(&g1g, &g2g), &pair(&g1g, &g2g)]));
    for i in 0..6 {
        let (a, b) = (rand_scalar(&mut rng), rand_scalar(&mut rng));
        let (pa, qb) = (point::<G1>(&a), point::<G2>(&b));
        c.run("pairing_check", &format!("random-single-{i}"), &pair(&pa, &qb));
        c.run("pairing_check", &format!("swap-true-{i}"), &cat(&[&pair(&pa, &qb), &pair(&G1::neg(&point::<G1>(&b)), &point::<G2>(&a))]));
        c.run("pairing_check", &format!("swap-false-{i}"), &cat(&[&pair(&pa, &qb), &pair(&point::<G1>(&b), &point::<G2>(&a))]));
        c.run("pairing_check", &format!("scalar-move-true-{i}"), &cat(&[&pair(&pa, &g2g), &pair(&G1::neg(&g1g), &point::<G2>(&a))]));
        c.run("pairing_check", &format!("scalar-move-false-{i}"), &cat(&[&pair(&pa, &g2g), &pair(&g1g, &point::<G2>(&a))]));
    }
    for n in [3usize, 4, 5, 8, 10] {
        let q2 = point::<G2>(&rand_scalar(&mut rng));
        let mut acc = blst_p1::default();
        let mut data = vec![];
        for _ in 0..n - 1 {
            let a = point::<G1>(&rand_scalar(&mut rng));
            acc = G1::add(&acc, &a);
            data.extend(pair(&a, &q2));
        }
        let mut good = data.clone();
        good.extend(pair(&G1::neg(&acc), &q2));
        c.run("pairing_check", &format!("sum-true-{n}"), &good);
        let mut bad = data.clone();
        bad.extend(pair(&G1::neg(&G1::add(&acc, &g1g)), &q2));
        c.run("pairing_check", &format!("sum-false-{n}"), &bad);
        let mut padded = good.clone();
        padded.extend(cat(&[&inf1, &bytes::<G2>(&q2)]));
        padded.extend(cat(&[&bytes::<G1>(&g1g), &inf2]));
        c.run("pairing_check", &format!("sum-true-{n}-with-infinities"), &padded);
        let mut random = vec![];
        for _ in 0..n {
            random.extend(pair(&point::<G1>(&rand_scalar(&mut rng)), &point::<G2>(&rand_scalar(&mut rng))));
        }
        c.run("pairing_check", &format!("random-{n}"), &random);
    }
    let ok = pair(&g1g, &g2g);
    let off1 = off_group::<G1>(&mut rng).1;
    let off2 = off_group::<G2>(&mut rng).1;
    let p1b = bytes::<G1>(&point::<G1>(&rand_scalar(&mut rng)));
    let p2b = bytes::<G2>(&point::<G2>(&rand_scalar(&mut rng)));
    c.run("pairing_check", "off-group-g1", &cat(&[&off1, &p2b]));
    c.run("pairing_check", "off-group-g2", &cat(&[&p1b, &off2]));
    c.run("pairing_check", "off-group-g1-inf-g2", &cat(&[&off1, &inf2]));
    c.run("pairing_check", "off-group-g2-inf-g1", &cat(&[&inf1, &off2]));
    c.run("pairing_check", "off-group-g1-after-good", &cat(&[&ok, &off1, &p2b]));
    c.run("pairing_check", "off-group-g2-after-good", &cat(&[&ok, &p1b, &off2]));
    for sign in [0u8, 1] {
        let mut x = vec![0u8; 48];
        x[0] = 0x80 | (sign << 5);
        if let Some(a) = G1::uncompress(&x) {
            c.run("pairing_check", &format!("corner-g1-{sign}"), &cat(&[&G1::serialize(&a), &p2b]));
        }
        let mut x = vec![0u8; 96];
        x[0] = 0x80 | (sign << 5);
        if let Some(a) = G2::uncompress(&x) {
            c.run("pairing_check", &format!("corner-g2-{sign}"), &cat(&[&p1b, &G2::serialize(&a)]));
        }
    }
    let flags = [0x80u8, 0x20, 0x40];
    for fl in flags {
        c.run("pairing_check", &format!("g1-flag-{fl:#x}"), &cat(&[&flag(&p1b, fl), &p2b]));
        c.run("pairing_check", &format!("g2-flag-{fl:#x}"), &cat(&[&p1b, &flag(&p2b, fl)]));
    }
    c.run("pairing_check", "g1-compressed-form", &cat(&[&comp::<G1>(&point::<G1>(&rand_scalar(&mut rng))), &vec![0u8; 48], &p2b]));
    c.run("pairing_check", "g1-infinity-flag-with-data", &cat(&[&flag(&p1b, 0x40), &p2b]));
    c.run("pairing_check", "g2-infinity-trailing", &cat(&[&p1b, &{ let mut o = inf2.clone(); o[191] = 1; o }]));
    c.run("pairing_check", "g1-infinity-trailing", &cat(&[&{ let mut o = inf1.clone(); o[95] = 1; o }, &p2b]));
    for k in 0..2 {
        for (n, v) in [("p", p.clone()), ("ff", vec![0xff; 48]), ("p+1", add_small(&p, 1))] {
            let mut a = p1b.clone();
            a[k * 48..k * 48 + 48].copy_from_slice(&v);
            c.run("pairing_check", &format!("g1-word{k}-{n}"), &cat(&[&a, &p2b]));
        }
    }
    for k in 0..4 {
        for (n, v) in [("p", p.clone()), ("ff", vec![0xff; 48])] {
            let mut a = p2b.clone();
            a[k * 48..k * 48 + 48].copy_from_slice(&v);
            c.run("pairing_check", &format!("g2-word{k}-{n}"), &cat(&[&p1b, &a]));
        }
    }
    c.run("pairing_check", "g2-swapped-components", &cat(&[&p1b, &p2b[48..96], &p2b[..48], &p2b[96..]]));
    c.run("pairing_check", "g2-swapped-halves", &cat(&[&p1b, &p2b[96..], &p2b[..96]]));
    c.run("pairing_check", "g1-swapped-halves", &cat(&[&p1b[48..], &p1b[..48], &p2b]));
    c.run("pairing_check", "all-zero", &vec![0u8; 288]);
    c.run("pairing_check", "all-ff", &vec![0xffu8; 288]);
    for len in [1, 95, 96, 191, 192, 287, 289, 575, 577] {
        let mut d = ok.repeat(3);
        d.truncate(len);
        while d.len() < len {
            d.push(9);
        }
        c.run("pairing_check", &format!("length-{len}"), &d);
    }
}
