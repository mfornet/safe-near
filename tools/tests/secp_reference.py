"""secp256k1 in plain Python integers: an independent check of the oracle's secp256k1 data."""

P = 2**256 - 2**32 - 977
N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
G = (0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
     0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)


def ec_add(a, b):
    """Affine addition; None is the point at infinity."""
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and (a[1] + b[1]) % P == 0:
        return None
    if a == b:
        m = 3 * a[0] * a[0] * pow(2 * a[1], -1, P) % P
    else:
        m = (b[1] - a[1]) * pow(b[0] - a[0], -1, P) % P
    x = (m * m - a[0] - b[0]) % P
    return x, (m * (a[0] - x) - a[1]) % P


def ec_mul(k, point):
    result = None
    while k:
        if k & 1:
            result = ec_add(result, point)
        point = ec_add(point, point)
        k >>= 1
    return result


def verify(public, msg, r, s):
    """Textbook ECDSA verification of the 32-byte `msg` under `public = (x, y)`; low `s` only, as
    libsecp256k1's `secp256k1_ecdsa_verify` requires."""
    if not (0 < r < N and 0 < s <= (N - 1) // 2) or len(msg) != 32:
        return False
    w = pow(s, -1, N)
    m = int.from_bytes(msg, "big") % N
    point = ec_add(ec_mul(m * w % N, G), ec_mul(r * w % N, public))
    return point is not None and point[0] % N == r
