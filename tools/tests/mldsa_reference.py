"""ML-DSA-65 (FIPS 204, final) in plain Python integers and `hashlib`, written from the standard.

Used by `test_crypto_fixtures.py` to recompute the keys, signatures and verdicts of
`near-lean/crypto/fixtures/mldsa.jsonl` independently of the Lean code and of AWS-LC. Pure mode with an
empty context, as `near-crypto` 0.37.4 calls it. Slow (about 20 ms a verification) and meant to be read.
"""

import hashlib

Q = 8380417
D = 13
TAU = 49
K, L = 6, 5
ETA = 4
GAMMA1 = 1 << 19
GAMMA2 = (Q - 1) // 32
BETA = TAU * ETA
OMEGA = 55
CT = 48
PK_LEN, SK_LEN, SIG_LEN = 1952, 4032, 3309


def shake(alg, data, n):
    return hashlib.new(alg, data).digest(n)


def brv8(n):
    return int(format(n, "08b")[::-1], 2)


ZETAS = [pow(1753, brv8(i), Q) for i in range(256)]


def ntt(f):
    w = list(f)
    m = 0
    length = 128
    while length >= 1:
        for start in range(0, 256, 2 * length):
            m += 1
            z = ZETAS[m]
            for j in range(start, start + length):
                t = z * w[j + length] % Q
                w[j + length] = (w[j] - t) % Q
                w[j] = (w[j] + t) % Q
        length //= 2
    return w


def intt(f):
    w = list(f)
    m = 256
    length = 1
    while length < 256:
        for start in range(0, 256, 2 * length):
            m -= 1
            z = -ZETAS[m] % Q
            for j in range(start, start + length):
                t = w[j]
                w[j] = (t + w[j + length]) % Q
                w[j + length] = z * (t - w[j + length]) % Q
        length *= 2
    inv256 = pow(256, -1, Q)
    return [x * inv256 % Q for x in w]


def mod_pm(r, m):
    r %= m
    return r - m if r > m // 2 else r


def power2round(r):
    r0 = mod_pm(r, 1 << D)
    return (r - r0) >> D, r0


def decompose(r):
    r %= Q
    r0 = mod_pm(r, 2 * GAMMA2)
    if r - r0 == Q - 1:
        return 0, r0 - 1
    return (r - r0) // (2 * GAMMA2), r0


def use_hint(h, r):
    m = (Q - 1) // (2 * GAMMA2)
    r1, r0 = decompose(r)
    if h and r0 > 0:
        return (r1 + 1) % m
    if h:
        return (r1 - 1) % m
    return r1


def make_hint(z, r):
    return decompose(r)[0] != decompose(r + z)[0]


def stream(alg, seed, parse, count=256):
    n = 1024
    while True:
        out = parse(shake(alg, seed, n))
        if len(out) >= count:
            return out[:count]
        n *= 2


def parse_ntt(data):
    out = []
    for i in range(0, len(data) - 2, 3):
        z = data[i] | data[i + 1] << 8 | (data[i + 2] & 0x7F) << 16
        if z < Q:
            out.append(z)
    return out


def parse_bounded(data):
    out = []
    for b in data:
        for nib in (b & 15, b >> 4):
            if nib < 9:
                out.append(ETA - nib)
    return out


def expand_a(rho):
    return [[stream("shake_128", rho + bytes([s, r]), parse_ntt) for s in range(L)] for r in range(K)]


def expand_s(rho):
    def poly(i):
        return stream("shake_256", rho + i.to_bytes(2, "little"), parse_bounded)
    return [poly(r) for r in range(L)], [poly(r + L) for r in range(K)]


def pack(values, bits):
    acc = 0
    for i, v in enumerate(values):
        acc |= v << (bits * i)
    return acc.to_bytes(len(values) * bits // 8, "little")


def unpack(data, bits, count=256):
    acc = int.from_bytes(data, "little")
    return [(acc >> (bits * i)) & ((1 << bits) - 1) for i in range(count)]


def expand_mask(rho, mu):
    return [[GAMMA1 - v for v in unpack(shake("shake_256", rho + (mu + r).to_bytes(2, "little"), 640), 20)]
            for r in range(L)]


def sample_in_ball(rho):
    n = 400
    while True:
        s = shake("shake_256", rho, n)
        signs = int.from_bytes(s[:8], "little")
        c = [0] * 256
        pos = 8
        ok = True
        for i in range(256 - TAU, 256):
            while pos < len(s) and s[pos] > i:
                pos += 1
            if pos >= len(s):
                ok = False
                break
            j = s[pos]
            pos += 1
            c[i] = c[j]
            c[j] = -1 if (signs >> (i + TAU - 256)) & 1 else 1
        if ok:
            return c
        n *= 2


def mat_vec(a, vhat):
    out = []
    for row in a:
        acc = [0] * 256
        for aij, vj in zip(row, vhat):
            acc = [(x + y * z) % Q for x, y, z in zip(acc, aij, vj)]
        out.append(acc)
    return out


def vadd(a, b):
    return [[(x + y) % Q for x, y in zip(p, q)] for p, q in zip(a, b)]


def vsub(a, b):
    return [[(x - y) % Q for x, y in zip(p, q)] for p, q in zip(a, b)]


def key_gen(xi):
    seed = shake("shake_256", xi + bytes([K, L]), 128)
    rho, rho_prime, key = seed[:32], seed[32:96], seed[96:]
    s1, s2 = expand_s(rho_prime)
    t = vadd([intt(p) for p in mat_vec(expand_a(rho), [ntt(p) for p in s1])], s2)
    t1 = [[power2round(x)[0] for x in p] for p in t]
    t0 = [[power2round(x)[1] for x in p] for p in t]
    pk = rho + b"".join(pack(p, 10) for p in t1)
    tr = shake("shake_256", pk, 64)
    sk = (rho + key + tr + b"".join(pack([ETA - x for x in p], 4) for p in s1 + s2)
          + b"".join(pack([(1 << (D - 1)) - x for x in p], 13) for p in t0))
    return pk, sk


def decode_sk(sk):
    rho, key, tr = sk[:32], sk[32:64], sk[64:128]
    pos = 128

    def take(n, bits, offset):
        nonlocal pos
        polys = []
        for _ in range(n):
            size = 32 * bits
            polys.append([offset - v for v in unpack(sk[pos:pos + size], bits)])
            pos += size
        return polys
    s1 = take(L, 4, ETA)
    s2 = take(K, 4, ETA)
    t0 = take(K, 13, 1 << (D - 1))
    return rho, key, tr, s1, s2, t0


def public_key_of_secret(sk):
    """What AWS-LC's `pk_from_sk` returns: `None` unless s1, s2 are within eta and t0, tr are recomputed ones."""
    if len(sk) != SK_LEN:
        return None
    rho, _, tr, s1, s2, t0 = decode_sk(sk)
    if any(abs(x) > ETA for p in s1 + s2 for x in p):
        return None
    t = vadd([intt(p) for p in mat_vec(expand_a(rho), [ntt(p) for p in s1])], s2)
    pk = rho + b"".join(pack([power2round(x)[0] for x in p], 10) for p in t)
    if shake("shake_256", pk, 64) != tr:
        return None
    if [[power2round(x)[1] for x in p] for p in t] != t0:
        return None
    return pk


def w1_encode(w1):
    return b"".join(pack(p, 4) for p in w1)


def hint_pack(h):
    ys, counts = [], []
    for p in h:
        ys += [j for j in range(256) if p[j]]
        counts.append(len(ys))
    return bytes(ys) + bytes(OMEGA - len(ys)) + bytes(counts)


def hint_unpack(y):
    h = [[0] * 256 for _ in range(K)]
    index = 0
    for i in range(K):
        if y[OMEGA + i] < index or y[OMEGA + i] > OMEGA:
            return None
        first = index
        while index < y[OMEGA + i]:
            if index > first and y[index - 1] >= y[index]:
                return None
            h[i][y[index]] = 1
            index += 1
    if any(y[i] for i in range(index, OMEGA)):
        return None
    return h


def sign_internal(sk, m_prime, rnd):
    rho, key, tr, s1, s2, t0 = decode_sk(sk)
    a = expand_a(rho)
    s1h, s2h, t0h = [ntt(p) for p in s1], [ntt(p) for p in s2], [ntt(p) for p in t0]
    mu = shake("shake_256", tr + m_prime, 64)
    rho2 = shake("shake_256", key + rnd + mu, 64)
    kappa = 0
    for _ in range(13106):
        y = expand_mask(rho2, kappa)
        w = [intt(p) for p in mat_vec(a, [ntt(p) for p in y])]
        w1 = [[decompose(x)[0] for x in p] for p in w]
        ct = shake("shake_256", mu + w1_encode(w1), CT)
        chat = ntt(sample_in_ball(ct))

        def times(vh):
            return [intt([c * x % Q for c, x in zip(chat, p)]) for p in vh]
        cs1, cs2 = times(s1h), times(s2h)
        z = [[mod_pm(a_ + b_, Q) for a_, b_ in zip(p, q)] for p, q in zip(y, cs1)]
        r0 = [[decompose(x)[1] for x in p] for p in vsub(w, cs2)]
        kappa += L
        if max(abs(x) for p in z for x in p) >= GAMMA1 - BETA:
            continue
        if max(abs(x) for p in r0 for x in p) >= GAMMA2 - BETA:
            continue
        ct0 = times(t0h)
        r = vadd(vsub(w, cs2), ct0)
        h = [[1 if make_hint(-c, x) else 0 for c, x in zip(cp, rp)] for cp, rp in zip(ct0, r)]
        if max(abs(mod_pm(x, Q)) for p in ct0 for x in p) >= GAMMA2 or sum(map(sum, h)) > OMEGA:
            continue
        return ct + b"".join(pack([GAMMA1 - x for x in p], 20) for p in z) + hint_pack(h)
    return None


def verify_internal(pk, m_prime, sig):
    if len(pk) != PK_LEN or len(sig) != SIG_LEN:
        return False
    rho = pk[:32]
    t1 = [unpack(pk[32 + 320 * i:32 + 320 * (i + 1)], 10) for i in range(K)]
    ct = sig[:CT]
    z = [[GAMMA1 - v for v in unpack(sig[CT + 640 * i:CT + 640 * (i + 1)], 20)] for i in range(L)]
    h = hint_unpack(sig[CT + 640 * L:])
    if h is None or max(abs(x) for p in z for x in p) >= GAMMA1 - BETA:
        return False
    mu = shake("shake_256", shake("shake_256", pk, 64) + m_prime, 64)
    chat = ntt(sample_in_ball(ct))
    az = mat_vec(expand_a(rho), [ntt([x % Q for x in p]) for p in z])
    ct1 = [[c * x % Q for c, x in zip(chat, ntt([v << D for v in p]))] for p in t1]
    w = [intt(p) for p in vsub(az, ct1)]
    w1 = [[use_hint(hv, x) for hv, x in zip(hp, wp)] for hp, wp in zip(h, w)]
    return ct == shake("shake_256", mu + w1_encode(w1), CT)


def sign(sk, msg, rnd):
    return sign_internal(sk, b"\x00\x00" + msg, rnd)


def verify(pk, msg, sig):
    return verify_internal(pk, b"\x00\x00" + msg, sig)
