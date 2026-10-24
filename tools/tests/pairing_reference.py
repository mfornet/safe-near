"""Pairing-friendly curves in plain Python integers: BN254 (alt_bn128) and BLS12-381.

An independent reference for `near-lean/crypto` (it shares no code with it): the fields Fp, Fp2 =
Fp[u]/(u^2 + 1) and Fp12 = Fp[w]/(w^12 - 2 a w^6 + a^2 + 1) (a flat polynomial, w^6 = a + u), the
groups G1 and G2 (the twist, affine), the optimal ate pairing with the final exponentiation
computed as one power, and the bilinear check the host functions perform.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Curve:
    name: str
    p: int
    r: int
    b: int  # E: y^2 = x^3 + b
    a: int  # xi = a + u, w^6 = xi
    d_twist: bool  # D-type twist (E': y^2 = x^3 + b / xi) or M-type (b * xi)
    loop: int  # |6x + 2| (BN) or |x| (BLS)
    bn: bool
    x_negative: bool = False

    @property
    def b2(self):
        # b' as an Fp2 element (c0, c1)
        xi = (self.a, 1)
        if self.d_twist:
            return fp2_mul((self.b, 0), fp2_inv(self.p, xi), self.p)
        return fp2_mul((self.b, 0), xi, self.p)


def fp2_add(x, y, p):
    return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)


def fp2_sub(x, y, p):
    return ((x[0] - y[0]) % p, (x[1] - y[1]) % p)


def fp2_neg(x, p):
    return ((-x[0]) % p, (-x[1]) % p)


def fp2_mul(x, y, p):
    return ((x[0] * y[0] - x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)


def fp2_inv(p, x):
    n = pow((x[0] * x[0] + x[1] * x[1]) % p, p - 2, p)
    return ((x[0] * n) % p, (-x[1] * n) % p)


def fp2_pow(x, e, p):
    r = (1, 0)
    while e:
        if e & 1:
            r = fp2_mul(r, x, p)
        x = fp2_mul(x, x, p)
        e >>= 1
    return r


# ---- Fp12 as a flat polynomial of degree < 12 in w


def f12_mul(c, x, y):
    p, a = c.p, c.a
    t = [0] * 23
    for i, xi in enumerate(x):
        if xi:
            for j, yj in enumerate(y):
                t[i + j] += xi * yj
    # w^12 = 2 a w^6 - (a^2 + 1)
    for k in range(22, 11, -1):
        v = t[k] % p
        if v:
            t[k - 6] += 2 * a * v
            t[k - 12] -= (a * a + 1) * v
        t[k] = 0
    return [v % p for v in t[:12]]


def f12_one():
    return [1] + [0] * 11


def f12_pow(c, x, e):
    r = f12_one()
    while e:
        if e & 1:
            r = f12_mul(c, r, x)
        x = f12_mul(c, x, x)
        e >>= 1
    return r


def f12_from_fp2(c, z):
    # c0 + c1 u with u = w^6 - a
    r = [0] * 12
    r[0] = (z[0] - c.a * z[1]) % c.p
    r[6] = z[1] % c.p
    return r


def f12_w(k):
    r = [0] * 12
    r[k] = 1
    return r


def f12_add(c, x, y):
    return [(u + v) % c.p for u, v in zip(x, y)]


def f12_sub(c, x, y):
    return [(u - v) % c.p for u, v in zip(x, y)]


# ---- twist points (affine over Fp2); None is the point at infinity


def tw_add(c, P, Q):
    p = c.p
    if P is None:
        return Q
    if Q is None:
        return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2:
        if y1 != y2 or y1 == (0, 0):
            return None
        lam = fp2_mul(fp2_mul((3, 0), fp2_mul(x1, x1, p), p), fp2_inv(p, fp2_mul((2, 0), y1, p)), p)
    else:
        lam = fp2_mul(fp2_sub(y2, y1, p), fp2_inv(p, fp2_sub(x2, x1, p)), p)
    x3 = fp2_sub(fp2_sub(fp2_mul(lam, lam, p), x1, p), x2, p)
    y3 = fp2_sub(fp2_mul(lam, fp2_sub(x1, x3, p), p), y1, p)
    return (x3, y3)


def tw_neg(c, P):
    return None if P is None else (P[0], fp2_neg(P[1], c.p))


def tw_mul(c, P, k):
    R = None
    while k:
        if k & 1:
            R = tw_add(c, R, P)
        P = tw_add(c, P, P)
        k >>= 1
    return R


def tw_on_curve(c, P):
    if P is None:
        return True
    p = c.p
    x, y = P
    return fp2_mul(y, y, p) == fp2_add(fp2_mul(fp2_mul(x, x, p), x, p), c.b2, p)


def tw_frobenius(c, P):
    """The p-power Frobenius of the untwisted point, as a point of the twist."""
    p = c.p
    x, y = P
    xi = (c.a, 1)
    if c.d_twist:
        cx, cy = fp2_pow(xi, (p - 1) // 3, p), fp2_pow(xi, (p - 1) // 2, p)
    else:
        cx = fp2_inv(p, fp2_pow(xi, (p - 1) // 3, p))
        cy = fp2_inv(p, fp2_pow(xi, (p - 1) // 2, p))
    conj = lambda z: (z[0], (-z[1]) % p)
    return (fp2_mul(conj(x), cx, p), fp2_mul(conj(y), cy, p))


def untwist(c, P):
    x, y = P
    if c.d_twist:
        return f12_mul(c, f12_from_fp2(c, x), f12_w(2)), f12_mul(c, f12_from_fp2(c, y), f12_w(3))
    # M-type: (x / w^2, y / w^3) = (x w^4 / xi, y w^3 / xi)
    xi_inv = f12_from_fp2(c, fp2_inv(c.p, (c.a, 1)))
    return (f12_mul(c, f12_mul(c, f12_from_fp2(c, x), f12_w(4)), xi_inv),
            f12_mul(c, f12_mul(c, f12_from_fp2(c, y), f12_w(3)), xi_inv))


def line(c, T, Q, P):
    """The line through the twist points T and Q (the tangent if equal) at the G1 point P, in Fp12."""
    p = c.p
    (tx, ty), (qx, qy) = T, Q
    if tx == qx:
        lam = fp2_mul(fp2_mul((3, 0), fp2_mul(tx, tx, p), p), fp2_inv(p, fp2_mul((2, 0), ty, p)), p)
    else:
        lam = fp2_mul(fp2_sub(qy, ty, p), fp2_inv(p, fp2_sub(qx, tx, p)), p)
    X, Y = untwist(c, T)
    # the slope of the untwisted line is lam * w (D) or lam / w (M)
    if c.d_twist:
        L = f12_mul(c, f12_from_fp2(c, lam), f12_w(1))
    else:
        L = f12_mul(c, f12_mul(c, f12_from_fp2(c, lam), f12_w(5)), f12_from_fp2(c, fp2_inv(p, (c.a, 1))))
    px, py = [P[0] % p] + [0] * 11, [P[1] % p] + [0] * 11
    return f12_sub(c, f12_sub(c, py, Y), f12_mul(c, L, f12_sub(c, px, X)))


def miller(c, Q, P):
    """Product of the line functions of the optimal ate loop of Q at P (both finite)."""
    if c.x_negative:
        P = (P[0], (-P[1]) % c.p)
    f = f12_one()
    T = Q
    for bit in bin(c.loop)[3:]:
        f = f12_mul(c, f12_mul(c, f, f), line(c, T, T, P))
        T = tw_add(c, T, T)
        if bit == "1":
            f = f12_mul(c, f, line(c, T, Q, P))
            T = tw_add(c, T, Q)
    if c.bn:
        Q1 = tw_frobenius(c, Q)
        Q2 = tw_neg(c, tw_frobenius(c, Q1))
        f = f12_mul(c, f, line(c, T, Q1, P))
        T = tw_add(c, T, Q1)
        f = f12_mul(c, f, line(c, T, Q2, P))
    return f


def final_exp(c, f):
    return f12_pow(c, f, (c.p**12 - 1) // c.r)


def pairing_product_is_one(c, pairs):
    """Whether the product of e(P, Q) over the pairs (P in G1 as (x, y) or None, Q in G2 or None) is one."""
    f = f12_one()
    for P, Q in pairs:
        if P is None or Q is None:
            continue
        f = f12_mul(c, f, miller(c, Q, P))
    return final_exp(c, f) == f12_one()


BN254 = Curve(
    "bn254",
    p=21888242871839275222246405745257275088696311157297823662689037894645226208583,
    r=21888242871839275222246405745257275088548364400416034343698204186575808495617,
    b=3, a=9, d_twist=True, loop=29793968203157093288, bn=True)

_BLS_X = 0xD201000000010000
BLS12381 = Curve(
    "bls12381",
    p=0x1A0111EA397FE69A4B1BA7B6434BACD764774B84F38512BF6730D2A0F6B0F6241EABFFFEB153FFFFB9FEFFFFFFFFAAAB,
    r=0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001,
    b=4, a=1, d_twist=False, loop=_BLS_X, bn=False, x_negative=True)


def g1_on_curve(c, P):
    return P is None or (P[1] * P[1] - P[0] ** 3 - c.b) % c.p == 0


def g1_add(c, P, Q):
    p = c.p
    if P is None:
        return Q
    if Q is None:
        return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2:
        if (y1 + y2) % p == 0:
            return None
        lam = 3 * x1 * x1 * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def g1_mul(c, P, k):
    R = None
    while k:
        if k & 1:
            R = g1_add(c, R, P)
        P = g1_add(c, P, P)
        k >>= 1
    return R
