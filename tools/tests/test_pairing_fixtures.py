"""The committed pairing, hash-to-curve and P-256 fixtures (`near-lean/crypto/fixtures`), recomputed
in plain Python integers with `pairing_reference.py` and the rules of `NearCrypto` written out again
(the encodings of `zeropool-bn` and `blst`, `ecdsa` 0.16.9): the oracle (`near-vm-runner`'s host
functions) and this reference agree on every checked line. Long inputs (many points, many pairs)
are checked on a sample; the Lean tests run them all."""

import functools
import json
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pairing_reference import (BLS12381, BN254, fp2_add, fp2_inv, fp2_mul, fp2_neg, fp2_sub,  # noqa: E402
                               g1_add, g1_mul, g1_on_curve, pairing_product_is_one, tw_add,
                               tw_mul, tw_neg, tw_on_curve)
import test_bls_isogeny  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "near-lean/crypto/fixtures"
HEX = re.compile(r"^(?:[0-9a-f]{2})*$")


def lines(name):
    return [json.loads(line) for line in (FIXTURES / name).read_text().splitlines()]


# ---------------------------------------------------------------------------------------------
# alt_bn128 (little-endian words, zeropool-bn 0.5.11)


def bn_le(b):
    return int.from_bytes(b, "little")


def bn_g1(raw):
    """A point of G1 (None is infinity), or False for an invalid encoding."""
    c = BN254
    x, y = bn_le(raw[:32]), bn_le(raw[32:])
    if x >= c.p or y >= c.p:
        return False
    if x == 0 and y == 0:
        return None
    return (x, y) if g1_on_curve(c, (x, y)) else False


@functools.lru_cache(maxsize=None)
def bn_in_g2(q):
    return tw_mul(BN254, q, BN254.r) is None


def bn_g2(raw):
    c = BN254
    v = [bn_le(raw[32 * k:32 * k + 32]) for k in range(4)]
    if any(t >= c.p for t in v):
        return False
    if not any(v):
        return None
    q = ((v[0], v[1]), (v[2], v[3]))
    return q if tw_on_curve(c, q) and bn_in_g2(q) else False


def bn_enc(pt):
    return bytes(64) if pt is None else pt[0].to_bytes(32, "little") + pt[1].to_bytes(32, "little")


def bn_g1_result(kind, data):
    c = BN254
    size = 96 if kind == "g1_multiexp" else 65
    if len(data) % size:
        return None
    acc = None
    for i in range(0, len(data), size):
        ch = data[i:i + size]
        if kind == "g1_multiexp":
            pt, k = bn_g1(ch[:64]), bn_le(ch[64:])
            if pt is False or k >= c.r:
                return None
            acc = g1_add(c, acc, g1_mul(c, pt, k))
        else:
            if ch[0] > 1:
                return None
            pt = bn_g1(ch[1:])
            if pt is False:
                return None
            if ch[0] == 1 and pt is not None:
                pt = (pt[0], (-pt[1]) % c.p)
            acc = g1_add(c, acc, pt)
    return bn_enc(acc)


def bn_pairing_result(data):
    if len(data) % 192:
        return None
    pairs = []
    for i in range(0, len(data), 192):
        a, q = bn_g1(data[i:i + 64]), bn_g2(data[i + 64:i + 192])
        if a is False or q is False:
            return None
        pairs.append((a, q))
    return pairs


# ---------------------------------------------------------------------------------------------
# BLS12-381 (big-endian words with the ZCash flags, blst 0.3.11)

B = BLS12381
P = B.p


def be(b):
    return int.from_bytes(b, "big")


def fp_bytes(x):
    return x.to_bytes(48, "big")


def sqrt_fp(a):
    y = pow(a, (P + 1) // 4, P)
    return y if y * y % P == a % P else None


def sqrt_fp2(z):
    a0, a1 = z
    if a1 == 0:
        r = sqrt_fp(a0)
        if r is not None:
            return (r, 0)
        r = sqrt_fp(-a0 % P)
        return (0, r) if r is not None else None
    s = sqrt_fp((a0 * a0 + a1 * a1) % P)
    if s is None:
        return None
    half = pow(2, -1, P)
    t = (a0 + s) * half % P
    if pow(t, (P - 1) // 2, P) != 1:
        t = (a0 - s) * half % P
    x = sqrt_fp(t)
    if x is None:
        return None
    root = (x, a1 * pow(2 * x, -1, P) % P)
    return root if fp2_mul(root, root, P) == z else None


def large(y):
    return 2 * y > P if isinstance(y, int) else (2 * y[1] > P if y[1] else 2 * y[0] > P)


class Side:
    """G1 (`g = 1`) or G2 (`g = 2`) of BLS12-381 with blst's encodings."""

    def __init__(self, g):
        self.g = g
        self.size = 96 if g == 1 else 192
        self.comp = 48 if g == 1 else 96

    # arithmetic on affine points; None is infinity
    def add(self, a, b):
        return g1_add(B, a, b) if self.g == 1 else tw_add(B, a, b)

    def mul(self, a, k):
        return g1_mul(B, a, k) if self.g == 1 else tw_mul(B, a, k)

    def neg(self, a):
        if a is None:
            return None
        return (a[0], (-a[1]) % P) if self.g == 1 else tw_neg(B, a)

    @functools.lru_cache(maxsize=None)
    def in_group(self, a):
        return self.mul(a, B.r) is None

    def fe(self, raw):
        """Field elements (`raw` is 48 * k bytes) or None when one is not canonical."""
        v = [be(raw[48 * k:48 * k + 48]) for k in range(len(raw) // 48)]
        return None if any(t >= P for t in v) else v

    def on_curve(self, pt):
        if self.g == 1:
            return (pt[1] * pt[1] - pt[0] ** 3 - 4) % P == 0
        return tw_on_curve(B, pt)

    def rhs(self, x):
        if self.g == 1:
            return (x**3 + 4) % P
        return fp2_add(fp2_mul(fp2_mul(x, x, P), x, P), (4, 4), P)

    def sqrt(self, a):
        return sqrt_fp(a) if self.g == 1 else sqrt_fp2(a)

    def ser(self, pt):
        if pt is None:
            return bytes([0x40]) + bytes(self.size - 1)
        if self.g == 1:
            return fp_bytes(pt[0]) + fp_bytes(pt[1])
        (x0, x1), (y0, y1) = pt
        return fp_bytes(x1) + fp_bytes(x0) + fp_bytes(y1) + fp_bytes(y0)

    def parse(self, raw, version):
        """`blst_p_deserialize` as `parse_p` uses it: a point, None for infinity, False for an error."""
        in0 = raw[0]
        if in0 & 0x80:
            return False
        if in0 & 0xE0 == 0:
            f = self.fe(raw)
            if f is None:
                return False
            pt = (f[0], f[1]) if self.g == 1 else ((f[1], f[0]), (f[3], f[2]))
            if not self.on_curve(pt):
                return False
            if self.g == 1 and pt[0] == 0 and version == 0:
                return False
            return pt
        if in0 == 0x40 and not any(raw[1:]):
            return None
        return False

    def uncompress(self, raw, version):
        in0 = raw[0]
        if in0 & 0x40:
            return None if (in0 & 0x3F == 0 and not any(raw[1:])) else False
        top = bytes([in0 & 0x1F]) + raw[1:]
        f = self.fe(top)
        if f is None:
            return False
        x = f[0] if self.g == 1 else (f[1], f[0])
        y = self.sqrt(self.rhs(x))
        if y is None:
            return False
        if large(y) != bool(in0 & 0x20):
            y = (P - y) % P if self.g == 1 else fp2_neg(y, P)
        if self.g == 1 and x == 0 and version == 0:
            return False
        return (x, y)


Side.__hash__ = lambda self: self.g
G = {1: Side(1), 2: Side(2)}


def bls_sum(side, data, version):
    item = 1 + side.size
    if len(data) % item:
        return "trap"
    acc = None
    for i in range(0, len(data), item):
        pt = side.parse(data[i + 1:i + item], version)
        if pt is False or data[i] > 1:
            return 1
        acc = side.add(acc, side.neg(pt) if data[i] == 1 else pt)
    return side.ser(acc)


def bls_multiexp(side, data, version):
    item = side.size + 32
    if len(data) % item:
        return "trap"
    acc = None
    for i in range(0, len(data), item):
        pt = side.parse(data[i:i + side.size], version)
        if pt is False or not side.in_group(pt):
            return 1
        acc = side.add(acc, side.mul(pt, int.from_bytes(data[i + side.size:i + item], "little")))
    return side.ser(acc)


def bls_decompress(side, data, version):
    if len(data) % side.comp:
        return "trap"
    out = b""
    for i in range(0, len(data), side.comp):
        raw = data[i:i + side.comp]
        if not raw[0] & 0x80:
            return 1
        pt = side.uncompress(raw, version)
        if pt is False:
            return 1
        out += side.ser(pt)
    return out


def sswu(a, b, z, u, field):
    """RFC 9380 section 6.6.2; `field` supplies the arithmetic."""
    F = field
    zu2 = F.mul(z, F.mul(u, u))
    tv1 = F.inv(F.add(F.mul(zu2, zu2), zu2))
    if F.is_zero(tv1):
        x1 = F.mul(b, F.inv(F.mul(z, a)))
    else:
        x1 = F.mul(F.neg(F.mul(b, F.inv(a))), F.add(F.one, tv1))
    gx = lambda x: F.add(F.mul(F.add(F.mul(x, x), a), x), b)
    x2 = F.mul(zu2, x1)
    y = F.sqrt(gx(x1))
    x = x1
    if y is None:
        x, y = x2, F.sqrt(gx(x2))
    if F.sgn0(u) != F.sgn0(y):
        y = F.neg(y)
    return x, y


class FieldFp:
    one = 1
    mul = staticmethod(lambda a, b: a * b % P)
    add = staticmethod(lambda a, b: (a + b) % P)
    neg = staticmethod(lambda a: (-a) % P)
    inv = staticmethod(lambda a: pow(a, -1, P) if a % P else 0)
    is_zero = staticmethod(lambda a: a % P == 0)
    sqrt = staticmethod(sqrt_fp)
    sgn0 = staticmethod(lambda a: a % 2 == 1)


class FieldFp2:
    one = (1, 0)
    mul = staticmethod(lambda a, b: fp2_mul(a, b, P))
    add = staticmethod(lambda a, b: fp2_add(a, b, P))
    neg = staticmethod(lambda a: fp2_neg(a, P))
    inv = staticmethod(lambda a: fp2_inv(P, a) if a != (0, 0) else (0, 0))
    is_zero = staticmethod(lambda a: a == (0, 0))
    sqrt = staticmethod(sqrt_fp2)
    sgn0 = staticmethod(lambda a: a[0] % 2 == 1 or (a[0] == 0 and a[1] % 2 == 1))


def poly(cs, monic, x, F):
    acc = F.one if monic else cs[-1]
    for c in reversed(cs if monic else cs[:-1]):
        acc = F.add(F.mul(acc, x), c)
    return acc


H_EFF = 0xBC69F08F2EE75B3584C6A0EA91B352888E2A8E9145AD7689986FF031508FFE1329C2F178731DB956D82BF015D1212B02EC0EC69D7477C1AE954CBC06689F6A359894C0ADEBBF6B4E8020005AAA95551


def map_to_g1(u, c):
    F = FieldFp
    xp, yp = sswu(c["a1"][0], c["b1"][0], 11, u, F)
    xd, yd = poly(c["xDen1"], True, xp, F), poly(c["yDen1"], True, xp, F)
    if xd == 0 or yd == 0:
        return None
    pt = (poly(c["xNum1"], False, xp, F) * pow(xd, -1, P) % P,
          yp * poly(c["yNum1"], False, xp, F) * pow(yd, -1, P) % P)
    return g1_mul(B, pt, 0xD201000000010001)


def map_to_g2(u, c):
    F = FieldFp2
    pairs = lambda k: [(c[k][2 * i], c[k][2 * i + 1]) for i in range(len(c[k]) // 2)]
    xp, yp = sswu(pairs("a2")[0], pairs("b2")[0], (P - 2, P - 1), u, F)
    xd, yd = poly(pairs("xDen2"), True, xp, F), poly(pairs("yDen2"), True, xp, F)
    if xd == (0, 0) or yd == (0, 0):
        return None
    pt = (F.mul(poly(pairs("xNum2"), False, xp, F), F.inv(xd)),
          F.mul(yp, F.mul(poly(pairs("yNum2"), False, xp, F), F.inv(yd))))
    return tw_mul(B, pt, H_EFF)


def bls_map(g, data):
    side = G[g]
    n = 48 if g == 1 else 96
    if len(data) % n:
        return "trap"
    c = test_bls_isogeny.constants()
    out = b""
    for i in range(0, len(data), n):
        f = side.fe(data[i:i + n])
        if f is None:
            return 1
        out += side.ser(map_to_g1(f[0], c) if g == 1 else map_to_g2((f[1], f[0]), c))
    return out


def bls_pairing(data):
    if len(data) % 288:
        return "trap"
    pairs = []
    for i in range(0, len(data), 288):
        a, q = G[1].parse(data[i:i + 96], 0), G[2].parse(data[i + 96:i + 288], 0)
        if a is False or q is False or not G[1].in_group(a) or not G[2].in_group(q):
            return 1
        pairs.append((a, q))
    return pairs


def expected(v):
    if v.get("trap"):
        return "trap"
    if "output" in v:
        return bytes.fromhex(v["output"])
    return b"" if v["ret"] == 0 else v["ret"]


# ---------------------------------------------------------------------------------------------
# P-256 (ecdsa 0.16.9 over p256 0.13.2)

P256_P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
P256_B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
P256_G = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
          0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5)


def p256_add(a, b):
    p = P256_P
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0]:
        if (a[1] + b[1]) % p == 0:
            return None
        lam = (3 * a[0] * a[0] - 3) * pow(2 * a[1], -1, p) % p
    else:
        lam = (b[1] - a[1]) * pow(b[0] - a[0], -1, p) % p
    x = (lam * lam - a[0] - b[0]) % p
    return (x, (lam * (a[0] - x) - a[1]) % p)


def p256_mul(a, k):
    r = None
    while k:
        if k & 1:
            r = p256_add(r, a)
        a = p256_add(a, a)
        k >>= 1
    return r


def p256_verify(sig, msg, pk):
    if len(sig) != 64:
        return "trap"
    r, s = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:], "big")
    if not (0 < r < P256_N and 0 < s < P256_N):
        return 0
    if len(pk) != 33:
        return "trap"
    x = int.from_bytes(pk[1:], "big")
    if pk[0] not in (2, 3) or x >= P256_P:
        return 0
    rhs = (x**3 - 3 * x + P256_B) % P256_P
    y = pow(rhs, (P256_P + 1) // 4, P256_P)
    if y * y % P256_P != rhs:
        return 0
    if y % 2 != pk[0] - 2:
        y = P256_P - y
    if len(msg) < 16:
        return 0
    z = int.from_bytes(msg[:32], "big") % P256_N
    si = pow(s, -1, P256_N)
    pt = p256_add(p256_mul(P256_G, z * si % P256_N), p256_mul((x, y), r * si % P256_N))
    return 1 if pt is not None and pt[0] % P256_N == r else 0


class FixtureReferenceTests(unittest.TestCase):
    def test_files_are_well_formed(self):
        for name, fields in (("bn254.jsonl", ("input",)), ("bls12381.jsonl", ("input",)),
                             ("p256.jsonl", ("sig", "msg", "pk"))):
            seen = set()
            for number, rec in enumerate(lines(name), 1):
                where = f"{name}:{number}"
                key = (rec["kind"], rec["name"], rec.get("sig"), rec.get("input"))
                self.assertTrue(key not in seen, where)
                seen.add(key)
                for f in fields:
                    self.assertRegex(rec[f], HEX, where)

    def test_bn254_g1_functions(self):
        n = 0
        for rec in lines("bn254.jsonl"):
            if rec["kind"] not in ("g1_multiexp", "g1_sum"):
                continue
            data = bytes.fromhex(rec["input"])
            if len(data) > 96 * 20:
                continue
            got = bn_g1_result(rec["kind"], data)
            want = bytes.fromhex(rec["output"]) if rec["ok"] else None
            self.assertEqual(got, want, rec["name"])
            n += 1
        self.assertGreater(n, 150)

    def test_bn254_pairing(self):
        evaluated = 0
        for rec in lines("bn254.jsonl"):
            if rec["kind"] != "pairing_check":
                continue
            data = bytes.fromhex(rec["input"])
            pairs = bn_pairing_result(data)
            if pairs is None:
                self.assertFalse(rec["ok"], rec["name"])
                continue
            self.assertTrue(rec["ok"], rec["name"])
            if sum(1 for a, q in pairs if a is not None and q is not None) > 2 or evaluated >= 3:
                continue
            self.assertEqual(pairing_product_is_one(BN254, pairs), rec["result"], rec["name"])
            evaluated += 1
        self.assertGreaterEqual(evaluated, 3)

    def test_bls12381_group_functions(self):
        checked = 0
        per_kind = {}
        for rec in lines("bls12381.jsonl"):
            kind = rec["kind"]
            if kind not in ("p1_sum", "p2_sum", "g1_multiexp", "g2_multiexp", "p1_decompress", "p2_decompress"):
                continue
            side = G[1 if kind[1] == "1" else 2]
            data = bytes.fromhex(rec["input"])
            if len(data) > (side.size + 33) * (2 if side.g == 2 else 4):
                continue
            if per_kind.get(kind, 0) >= 25:
                continue
            per_kind[kind] = per_kind.get(kind, 0) + 1
            for key, version in (("v0", 0), ("v1", 1)):
                f = {"p1_sum": bls_sum, "p2_sum": bls_sum, "g1_multiexp": bls_multiexp,
                     "g2_multiexp": bls_multiexp, "p1_decompress": bls_decompress,
                     "p2_decompress": bls_decompress}[kind]
                self.assertEqual(f(side, data, version), expected(rec[key]), f"{rec['name']} {kind} {key}")
            checked += 1
        self.assertGreater(checked, 100)

    def test_bls12381_hash_to_curve(self):
        checked = {"map_fp_to_g1": 0, "map_fp2_to_g2": 0}
        for rec in lines("bls12381.jsonl"):
            kind = rec["kind"]
            if kind not in checked or checked[kind] >= (30 if kind == "map_fp_to_g1" else 12):
                continue
            data = bytes.fromhex(rec["input"])
            if len(data) > 96:
                continue
            self.assertEqual(bls_map(1 if kind == "map_fp_to_g1" else 2, data), expected(rec["v1"]), rec["name"])
            checked[kind] += 1
        self.assertGreaterEqual(min(checked.values()), 10)

    def test_bls12381_pairing(self):
        evaluated = 0
        for rec in lines("bls12381.jsonl"):
            if rec["kind"] != "pairing_check":
                continue
            data = bytes.fromhex(rec["input"])
            pairs = bls_pairing(data)
            if pairs == "trap" or pairs == 1:
                self.assertEqual(rec["v1"].get("trap") and "trap" or rec["v1"]["ret"], pairs, rec["name"])
                continue
            if sum(1 for a, q in pairs if a is not None and q is not None) > 2 or evaluated >= 2:
                continue
            want = 0 if pairing_product_is_one(BLS12381, pairs) else 2
            self.assertEqual(rec["v1"]["ret"], want, rec["name"])
            evaluated += 1
        self.assertGreaterEqual(evaluated, 2)

    def test_p256_verify(self):
        count = 0
        for rec in lines("p256.jsonl"):
            got = p256_verify(bytes.fromhex(rec["sig"]), bytes.fromhex(rec["msg"]), bytes.fromhex(rec["pk"]))
            want = rec["result"] if rec["ok"] else "trap"
            self.assertEqual(got, want, rec["name"])
            count += 1
        self.assertGreater(count, 200)


if __name__ == "__main__":
    unittest.main()
