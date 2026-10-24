//! alt_bn128 (BN254) fixtures: `alt_bn128_g1_multiexp`, `alt_bn128_g1_sum` and
//! `alt_bn128_pairing_check` as `near-vm-runner` 0.37.4 runs them (`logic/alt_bn128.rs`, over
//! `zeropool-bn` 0.5.11). Inputs are built with that crate; every verdict is the host function's.

use super::crypto_vm::Vm;
use super::{hex, Out, Rng};
use bn::{AffineG1, AffineG2, Fq, Fq2, Fr, Group, G1, G2};
use serde_json::json;

const Q: &str = "21888242871839275222246405745257275088696311157297823662689037894645226208583";
const R: &str = "21888242871839275222246405745257275088548364400416034343698204186575808495617";

type B32 = [u8; 32];

/// A decimal number as 32 little-endian bytes.
fn dec(s: &str) -> B32 {
    let mut out = [0u8; 32];
    for c in s.bytes() {
        let mut carry = (c - b'0') as u32;
        for b in out.iter_mut() {
            let v = *b as u32 * 10 + carry;
            *b = v as u8;
            carry = v >> 8;
        }
    }
    out
}

fn add_small(a: &B32, k: u64) -> B32 {
    let mut out = *a;
    let mut carry = k as u128;
    for b in out.iter_mut() {
        let v = *b as u128 + (carry & 0xff);
        carry >>= 8;
        *b = v as u8;
        carry += v >> 8;
    }
    out
}

fn le(u: bn::arith::U256) -> B32 {
    let mut out = [0u8; 32];
    out[..16].copy_from_slice(&u.0[0].to_le_bytes());
    out[16..].copy_from_slice(&u.0[1].to_le_bytes());
    out
}

fn fq(x: Fq) -> B32 {
    le(x.into_u256())
}

fn fq2(x: Fq2) -> Vec<u8> {
    [fq(x.real()), fq(x.imaginary())].concat()
}

fn g1(p: G1) -> Vec<u8> {
    match AffineG1::from_jacobian(p) {
        Some(a) => [fq(a.x()), fq(a.y())].concat(),
        None => vec![0; 64],
    }
}

fn g2(q: G2) -> Vec<u8> {
    match AffineG2::from_jacobian(q) {
        Some(a) => [fq2(a.x()), fq2(a.y())].concat(),
        None => vec![0; 128],
    }
}

fn fr(x: Fr) -> B32 {
    le(x.into_u256())
}

fn rand_fr(rng: &mut Rng) -> Fr {
    Fr::random(&mut rng.0)
}

fn rand_g1(rng: &mut Rng) -> G1 {
    G1::one() * rand_fr(rng)
}

fn rand_g2(rng: &mut Rng) -> G2 {
    G2::one() * rand_fr(rng)
}

/// The coefficient `b'` of the twist `y² = x³ + b'`, from the generator.
fn twist_b() -> Fq2 {
    let g = AffineG2::from_jacobian(G2::one()).unwrap();
    g.y() * g.y() - g.x() * g.x() * g.x()
}

/// A point of the twist chosen by its abscissa that is on the curve, whatever its order.
fn twist_point(x: Fq2) -> Option<Vec<u8>> {
    let y = (x * x * x + twist_b()).sqrt()?;
    Some([fq2(x), fq2(y)].concat())
}

struct Ctx<'a> {
    out: &'a mut Out,
    vm: Vm,
    n: usize,
}

impl Ctx<'_> {
    fn g1(&mut self, multiexp: bool, name: &str, input: &[u8]) {
        let kind = if multiexp { "g1_multiexp" } else { "g1_sum" };
        let res = self.vm.bn_g1(multiexp, input);
        self.n += 1;
        self.out.push(
            kind,
            json!({"kind": kind, "name": name, "input": hex(input),
                   "ok": res.is_some(), "output": res.as_ref().map(|o| hex(o))}),
        );
    }

    fn pairing(&mut self, name: &str, input: &[u8]) {
        let res = self.vm.bn_pairing(input);
        self.out.push(
            "pairing_check",
            json!({"kind": "pairing_check", "name": name, "input": hex(input),
                   "ok": res.is_some(), "result": res}),
        );
    }
}

fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

pub fn bn254(out: &mut Out) {
    let mut rng = Rng::new(0x30);
    let q = dec(Q);
    let r = dec(R);
    let mut c = Ctx { out, vm: Vm::new(true), n: 0 };
    let g1gen = G1::one();
    let g2gen = G2::one();

    // ---- g1_multiexp
    let elem = |p: &[u8], s: &[u8]| cat(&[p, s]);
    c.g1(true, "empty", &[]);
    for (i, k) in ["0", "1", "2", "3", "5", "255", "65537"].iter().enumerate() {
        let s = fr(Fr::from_str(k).unwrap());
        c.g1(true, &format!("generator-times-{k}"), &elem(&g1(g1gen), &s));
        let p = rand_g1(&mut rng);
        c.g1(true, &format!("random-{i}-times-{k}"), &elem(&g1(p), &s));
    }
    let r_minus_1 = fr(Fr::zero() - Fr::one());
    c.g1(true, "generator-times-r-1", &elem(&g1(g1gen), &r_minus_1));
    c.g1(true, "random-times-r-1", &elem(&g1(rand_g1(&mut rng)), &r_minus_1));
    for (name, s) in [
        ("r", r),
        ("r+1", add_small(&r, 1)),
        ("r+2", add_small(&r, 2)),
        ("2^256-1", [0xff; 32]),
        ("2^255", {
            let mut b = [0u8; 32];
            b[31] = 0x80;
            b
        }),
        ("q", q),
    ] {
        c.g1(true, &format!("scalar-{name}"), &elem(&g1(g1gen), &s));
    }
    for n in (1..=12).chain([16, 17, 20, 31, 32, 33, 40, 64]) {
        let mut data = vec![];
        for _ in 0..n {
            data.extend(elem(&g1(rand_g1(&mut rng)), &fr(rand_fr(&mut rng))));
        }
        c.g1(true, &format!("random-{n}"), &data);
    }
    // special structure: repeats, negations, infinity, small scalars (doublings inside the sums)
    let p = rand_g1(&mut rng);
    let s = rand_fr(&mut rng);
    let one = fr(Fr::one());
    c.g1(true, "same-point-same-scalar-x2", &cat(&[&elem(&g1(p), &fr(s)), &elem(&g1(p), &fr(s))]));
    c.g1(true, "point-and-negation", &cat(&[&elem(&g1(p), &fr(s)), &elem(&g1(-p), &fr(s))]));
    c.g1(true, "point-and-negation-diff-scalars", &cat(&[&elem(&g1(p), &fr(s)), &elem(&g1(-p), &one)]));
    c.g1(true, "same-point-x5-scalar-1", &cat(&vec![elem(&g1(p), &one); 5].iter().map(|v| &v[..]).collect::<Vec<_>>()));
    let mut data = vec![];
    for k in 1..=9u64 {
        data.extend(elem(&g1(p), &fr(Fr::from_str(&k.to_string()).unwrap())));
    }
    c.g1(true, "same-point-scalars-1-to-9", &data);
    c.g1(true, "infinity", &elem(&[0; 64], &fr(s)));
    c.g1(true, "infinity-zero-scalar", &elem(&[0; 64], &[0; 32]));
    c.g1(true, "infinity-x3", &cat(&[&elem(&[0; 64], &fr(s)), &elem(&[0; 64], &fr(s)), &elem(&[0; 64], &one)]));
    c.g1(true, "infinity-and-point", &cat(&[&elem(&[0; 64], &fr(s)), &elem(&g1(p), &fr(s))]));
    c.g1(true, "point-zero-scalar", &elem(&g1(p), &[0; 32]));
    c.g1(true, "two-zero-scalars", &cat(&[&elem(&g1(p), &[0; 32]), &elem(&g1(g1gen), &[0; 32])]));
    let mut data = vec![];
    for _ in 0..8 {
        data.extend(elem(&g1(rand_g1(&mut rng)), &fr(Fr::zero() - Fr::one())));
    }
    c.g1(true, "eight-scalars-r-1", &data);
    // the points with x = 0, if y^2 = 3 has roots
    if let Some(y) = Fq::from_str("3").unwrap().sqrt() {
        for (name, yy) in [("y", y), ("-y", Fq::zero() - y)] {
            let pt = [fq(Fq::zero()), fq(yy)].concat();
            c.g1(true, &format!("x0-{name}"), &elem(&pt, &fr(s)));
            c.g1(false, &format!("x0-{name}"), &cat(&[&[0], &pt]));
        }
    }
    // invalid encodings
    let good = elem(&g1(p), &fr(s));
    for len in [1, 31, 32, 63, 64, 95, 97, 127, 128, 129, 191, 192, 193] {
        let mut d = good.repeat(3);
        d.truncate(len);
        while d.len() < len {
            d.push(7);
        }
        c.g1(true, &format!("length-{len}"), &d);
    }
    let pt = g1(p);
    let (px, py) = (pt[..32].to_vec(), pt[32..].to_vec());
    let bad_points: Vec<(String, Vec<u8>)> = vec![
        ("x-eq-q".into(), cat(&[&q, &py])),
        ("x-q+1".into(), cat(&[&add_small(&q, 1), &py])),
        ("y-eq-q".into(), cat(&[&px, &q])),
        ("y-2^256-1".into(), cat(&[&px, &[0xff; 32]])),
        ("both-ff".into(), vec![0xff; 64]),
        ("y-plus-q".into(), cat(&[&px, &le_add(&py, &q)])),
        ("y-plus-one".into(), cat(&[&px, &add_small(&py.clone().try_into().unwrap(), 1)])),
        ("x-plus-one".into(), cat(&[&add_small(&px.clone().try_into().unwrap(), 1), &py])),
        ("swapped".into(), cat(&[&py, &px])),
        ("1-1".into(), cat(&[&dec("1"), &dec("1")])),
        ("x0-y0-y-nonzero".into(), cat(&[&[0; 32], &dec("1")])),
        ("x-nonzero-y0".into(), cat(&[&dec("1"), &[0; 32]])),
        ("x-zero-y-q".into(), cat(&[&[0; 32], &q])),
        ("non-canonical-zero".into(), cat(&[&q, &q])),
    ];
    for (name, bp) in &bad_points {
        let s = fr(s);
        c.g1(true, &format!("bad-{name}"), &elem(bp, &s));
        c.g1(true, &format!("bad-{name}-after-good"), &cat(&[&good, &elem(bp, &s)]));
        c.g1(true, &format!("bad-{name}-before-good"), &cat(&[&elem(bp, &s), &good]));
        c.g1(false, &format!("bad-{name}"), &cat(&[&[0], bp]));
        c.g1(false, &format!("bad-{name}-negative"), &cat(&[&[1], bp]));
    }

    // ---- g1_sum
    let sgn = |neg: u8, p: &[u8]| cat(&[&[neg], p]);
    c.g1(false, "empty", &[]);
    for neg in [0u8, 1] {
        c.g1(false, &format!("generator-sign-{neg}"), &sgn(neg, &g1(g1gen)));
        c.g1(false, &format!("random-sign-{neg}"), &sgn(neg, &g1(p)));
        c.g1(false, &format!("infinity-sign-{neg}"), &sgn(neg, &[0; 64]));
    }
    c.g1(false, "p-minus-p", &cat(&[&sgn(0, &g1(p)), &sgn(1, &g1(p))]));
    c.g1(false, "p-plus-neg-p", &cat(&[&sgn(0, &g1(p)), &sgn(0, &g1(-p))]));
    c.g1(false, "neg-p-minus-neg-p", &cat(&[&sgn(0, &g1(-p)), &sgn(1, &g1(-p))]));
    c.g1(false, "p-plus-p", &cat(&[&sgn(0, &g1(p)), &sgn(0, &g1(p))]));
    c.g1(false, "p-minus-neg-p", &cat(&[&sgn(0, &g1(p)), &sgn(1, &g1(-p))]));
    c.g1(false, "neg-p-neg-p", &cat(&[&sgn(1, &g1(p)), &sgn(1, &g1(p))]));
    c.g1(false, "double-then-cancel", &cat(&[&sgn(0, &g1(p)), &sgn(0, &g1(p)), &sgn(1, &g1(p)), &sgn(1, &g1(p))]));
    c.g1(false, "p-plus-inf", &cat(&[&sgn(0, &g1(p)), &sgn(0, &[0; 64])]));
    c.g1(false, "inf-plus-p", &cat(&[&sgn(1, &[0; 64]), &sgn(1, &g1(p))]));
    c.g1(false, "inf-x4", &sgn(0, &[0; 64]).repeat(4));
    let a = rand_g1(&mut rng);
    c.g1(false, "p-q-minus-p-q", &cat(&[&sgn(0, &g1(p)), &sgn(0, &g1(a)), &sgn(1, &g1(p)), &sgn(1, &g1(a))]));
    c.g1(false, "p-plus-q-plus-neg-sum", &cat(&[&sgn(0, &g1(p)), &sgn(0, &g1(a)), &sgn(0, &g1(-(p + a)))]));
    for n in (2..=12).chain([16, 33, 64]) {
        let mut data = vec![];
        for _ in 0..n {
            let neg = rng.array::<1>()[0] & 1;
            data.extend(sgn(neg, &g1(rand_g1(&mut rng))));
        }
        c.g1(false, &format!("random-{n}"), &data);
    }
    for sign in [2u8, 3, 0x80, 0xff] {
        c.g1(false, &format!("bad-sign-{sign}"), &sgn(sign, &g1(p)));
        c.g1(false, &format!("bad-sign-{sign}-after-good"), &cat(&[&sgn(0, &g1(p)), &sgn(sign, &g1(p))]));
    }
    c.g1(false, "bad-sign-and-bad-point", &sgn(2, &[0xff; 64]));
    for len in [1, 2, 64, 66, 129, 130, 131] {
        let mut d = sgn(0, &g1(p)).repeat(3);
        d.truncate(len);
        while d.len() < len {
            d.push(1);
        }
        c.g1(false, &format!("length-{len}"), &d);
    }
    for (name, bp) in &bad_points {
        c.g1(false, &format!("bad-{name}-middle"), &cat(&[&sgn(0, &g1(p)), &sgn(1, bp), &sgn(0, &g1(g1gen))]));
    }

    // ---- pairing_check
    let pair = |a: G1, b: G2| cat(&[&g1(a), &g2(b)]);
    c.pairing("empty", &[]);
    c.pairing("inf-inf", &pair(G1::zero(), G2::zero()));
    c.pairing("generator-inf", &pair(g1gen, G2::zero()));
    c.pairing("inf-generator", &pair(G1::zero(), g2gen));
    c.pairing("generators", &pair(g1gen, g2gen));
    c.pairing("generators-negated", &cat(&[&pair(g1gen, g2gen), &pair(-g1gen, g2gen)]));
    c.pairing("generators-negated-g2", &cat(&[&pair(g1gen, g2gen), &pair(g1gen, -g2gen)]));
    c.pairing("generators-twice", &cat(&[&pair(g1gen, g2gen), &pair(g1gen, g2gen)]));
    for i in 0..6 {
        let (a, b) = (rand_fr(&mut rng), rand_fr(&mut rng));
        let (pa, qb) = (g1gen * a, g2gen * b);
        c.pairing(&format!("random-single-{i}"), &pair(pa, qb));
        // e(aP, bQ) e(-bP, aQ) = 1; e(aP, Q) e(-P, aQ) = 1
        c.pairing(&format!("swap-true-{i}"), &cat(&[&pair(g1gen * a, g2gen * b), &pair(-(g1gen * b), g2gen * a)]));
        c.pairing(&format!("swap-false-{i}"), &cat(&[&pair(g1gen * a, g2gen * b), &pair(g1gen * b, g2gen * a)]));
        c.pairing(&format!("scalar-move-true-{i}"), &cat(&[&pair(g1gen * a, g2gen), &pair(-g1gen, g2gen * a)]));
        c.pairing(&format!("scalar-move-false-{i}"), &cat(&[&pair(g1gen * a, g2gen), &pair(-g1gen, g2gen * (a + Fr::one()))]));
    }
    for n in [3usize, 4, 5, 8, 10, 16] {
        // sum of the first n-1 scalars cancelled by the last: e(a_i P, Q) ... e(-(sum a_i) P, Q)
        let q2 = rand_g2(&mut rng);
        let mut data = vec![];
        let mut sum = Fr::zero();
        for _ in 0..n - 1 {
            let a = rand_fr(&mut rng);
            sum = sum + a;
            data.extend(pair(g1gen * a, q2));
        }
        let mut good = data.clone();
        good.extend(pair(-(g1gen * sum), q2));
        c.pairing(&format!("sum-true-{n}"), &good);
        let mut bad = data.clone();
        bad.extend(pair(-(g1gen * (sum + Fr::one())), q2));
        c.pairing(&format!("sum-false-{n}"), &bad);
        let mut padded = good.clone();
        padded.extend(pair(G1::zero(), q2));
        padded.extend(pair(g1gen, G2::zero()));
        c.pairing(&format!("sum-true-{n}-with-infinities"), &padded);
        let mut random = vec![];
        for _ in 0..n {
            random.extend(pair(rand_g1(&mut rng), rand_g2(&mut rng)));
        }
        c.pairing(&format!("random-{n}"), &random);
    }
    // the same pair twice with opposite signs in different positions
    let (a, b) = (rand_g1(&mut rng), rand_g2(&mut rng));
    c.pairing("cancel-adjacent", &cat(&[&pair(a, b), &pair(-a, b)]));
    c.pairing("cancel-far", &cat(&[&pair(a, b), &pair(rand_g1(&mut rng), g2gen), &pair(-a, b)]));
    // invalid encodings and points
    let ok = pair(g1gen, g2gen);
    for len in [1, 63, 64, 128, 191, 193, 255, 383, 385] {
        let mut d = ok.repeat(3);
        d.truncate(len);
        while d.len() < len {
            d.push(9);
        }
        c.pairing(&format!("length-{len}"), &d);
    }
    let g2b = g2(rand_g2(&mut rng));
    let g1b = g1(rand_g1(&mut rng));
    let mut bad_g1: Vec<(String, Vec<u8>)> = bad_points.iter().map(|(n, v)| (n.clone(), v.clone())).collect();
    bad_g1.truncate(8);
    for (name, bp) in &bad_g1 {
        c.pairing(&format!("bad-g1-{name}"), &cat(&[bp, &g2b]));
        c.pairing(&format!("bad-g1-{name}-after-good"), &cat(&[&ok, bp, &g2b]));
    }
    let word = |k: usize, v: &B32, base: &[u8]| {
        let mut d = base.to_vec();
        d[k * 32..k * 32 + 32].copy_from_slice(v);
        d
    };
    for k in 0..4 {
        for (name, v) in [("q", q), ("q+1", add_small(&q, 1)), ("ff", [0xff; 32])] {
            c.pairing(&format!("g2-word{k}-{name}"), &cat(&[&g1b, &word(k, &v, &g2b)]));
        }
        c.pairing(&format!("g2-word{k}-plus-one"), &cat(&[&g1b, &word(k, &add_small(&g2b[k * 32..k * 32 + 32].try_into().unwrap(), 1), &g2b)]));
    }
    c.pairing("g2-swapped-halves", &cat(&[&g1b, &g2b[64..], &g2b[..64]]));
    c.pairing("g2-swapped-components", &cat(&[&g1b, &g2b[32..64], &g2b[..32], &g2b[64..]]));
    c.pairing("g2-x-zero-y-nonzero", &cat(&[&g1b, &[0; 64], &g2b[64..]]));
    c.pairing("g2-y-zero-x-nonzero", &cat(&[&g1b, &g2b[..64], &[0; 64]]));
    c.pairing("g2-all-ff", &cat(&[&g1b, &[0xff; 128]]));
    // points of the twist outside the subgroup (the cofactor is not cleared), found by abscissa
    let mut found = 0;
    let mut tries = 0;
    while found < 6 && tries < 200 {
        tries += 1;
        let x = Fq2::new(Fq::random(&mut rng.0), Fq::random(&mut rng.0));
        if let Some(bp) = twist_point(x) {
            found += 1;
            c.pairing(&format!("twist-not-subgroup-{found}"), &cat(&[&g1b, &bp]));
            c.pairing(&format!("twist-not-subgroup-{found}-inf-g1"), &cat(&[&[0; 64], &bp]));
            c.pairing(&format!("twist-not-subgroup-{found}-after-good"), &cat(&[&ok, &g1b, &bp]));
            // the point is on the curve: flipping a coordinate bit puts it off the curve
            let mut off = bp.clone();
            off[0] ^= 1;
            c.pairing(&format!("twist-off-curve-{found}"), &cat(&[&g1b, &off]));
        }
    }
    // points with x = 0 on the twist, if y^2 = b' has roots
    if let Some(bp) = twist_point(Fq2::zero()) {
        c.pairing("twist-x0", &cat(&[&g1b, &bp]));
    }
    // a G1 point and G2 point of the right curves but swapped roles
    c.pairing("g1-bytes-as-g2", &cat(&[&g1b, &g1b, &g1b]));
    let _ = (px, py);
}

fn le_add(a: &[u8], b: &B32) -> B32 {
    let mut out = [0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let s = a[i] as u16 + b[i] as u16 + carry;
        out[i] = s as u8;
        carry = s >> 8;
    }
    out
}
