"""The hash-to-curve constants of `near-lean/crypto` (`NearCrypto/Bls12381/Isogeny.lean`) define
isogenies: random points of the SSWU curves are sent to points of BLS12-381's `E1` and `E2`."""

from pathlib import Path
import random
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pairing_reference import BLS12381, fp2_add, fp2_inv, fp2_mul, fp2_sub  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "near-lean/crypto/NearCrypto/Bls12381/Isogeny.lean"
P = BLS12381.p


def constants():
    text = SOURCE.read_text()
    out = {}
    for name, body in re.findall(r"def (\w+) : Array Nat :=\s*limbs\s*#\[(.*?)\]", text, re.S):
        words = [int(w, 16) for w in re.findall(r"0x([0-9a-f]+)", body)]
        assert len(words) % 6 == 0, name
        out[name] = [sum(words[6 * i + j] << (64 * j) for j in range(6)) for i in range(len(words) // 6)]
    return out


def sqrt_fp(a):
    y = pow(a, (P + 1) // 4, P)
    return y if y * y % P == a % P else None


def horner(cs, x, monic, mul, add, one):
    acc = one if monic else cs[-1]
    for c in reversed(cs if monic else cs[:-1]):
        acc = add(mul(acc, x), c)
    return acc


class IsogenyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.c = constants()

    def test_known_curve_constants(self):
        self.assertEqual(self.c["a1"], [0x144698A3B8E9433D693A02C96D4982B0EA985383EE66A8D8E8981AEFD881AC98936F8DA0E0F97F5CF428082D584C1D])
        self.assertEqual(self.c["b1"], [0x12E2908D11688030018B12E8753EEE3B2016C1F0F24F4070A0B9C14FCEF35EF55A23215A316CEAA5D1CC48E98E172BE0])
        self.assertEqual(self.c["a2"], [0, 240])
        self.assertEqual(self.c["b2"], [1012, 1012])
        self.assertEqual(len(self.c["xNum1"]), 12)
        self.assertEqual(len(self.c["xDen1"]), 10)
        self.assertEqual(len(self.c["yNum1"]), 16)
        self.assertEqual(len(self.c["yDen1"]), 15)
        self.assertEqual([len(self.c[k]) for k in ("xNum2", "xDen2", "yNum2", "yDen2")], [8, 4, 8, 6])

    def test_g1_isogeny_maps_to_e1(self):
        c = self.c
        a, b = c["a1"][0], c["b1"][0]
        mul = lambda x, y: x * y % P
        add = lambda x, y: (x + y) % P
        rnd = random.Random(1)
        checked = 0
        while checked < 20:
            x = rnd.randrange(P)
            y = sqrt_fp((x**3 + a * x + b) % P)
            if y is None:
                continue
            xd = horner(c["xDen1"], x, True, mul, add, 1)
            yd = horner(c["yDen1"], x, True, mul, add, 1)
            X = horner(c["xNum1"], x, False, mul, add, 1) * pow(xd, -1, P) % P
            Y = y * horner(c["yNum1"], x, False, mul, add, 1) * pow(yd, -1, P) % P
            self.assertEqual(Y * Y % P, (X**3 + 4) % P)
            checked += 1

    def test_g2_isogeny_maps_to_e2(self):
        c = self.c
        pairs = lambda k: [(c[k][2 * i], c[k][2 * i + 1]) for i in range(len(c[k]) // 2)]
        a, b = pairs("a2")[0], pairs("b2")[0]
        mul = lambda x, y: fp2_mul(x, y, P)
        add = lambda x, y: fp2_add(x, y, P)
        one = (1, 0)
        rnd = random.Random(2)

        def sqrt2(z):
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
            return root if mul(root, root) == z else None

        checked = 0
        tries = 0
        while checked < 10 and tries < 400:
            tries += 1
            x = (rnd.randrange(P), rnd.randrange(P))
            rhs = add(add(mul(mul(x, x), x), mul(a, x)), b)
            y = sqrt2(rhs)
            if y is None:
                continue
            xd = horner(pairs("xDen2"), x, True, mul, add, one)
            yd = horner(pairs("yDen2"), x, True, mul, add, one)
            X = mul(horner(pairs("xNum2"), x, False, mul, add, one), fp2_inv(P, xd))
            Y = mul(mul(y, horner(pairs("yNum2"), x, False, mul, add, one)), fp2_inv(P, yd))
            self.assertEqual(mul(Y, Y), add(mul(mul(X, X), X), (4, 4)))
            checked += 1
        self.assertGreater(checked, 3)


if __name__ == "__main__":
    unittest.main()
