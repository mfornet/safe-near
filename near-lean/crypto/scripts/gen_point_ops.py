#!/usr/bin/env python3
"""Generate NearCrypto/Secp256k1/PointOps.lean: the field arithmetic of the secp256k1 point
formulas with lazy reduction.

The formulas of `Jac.dbl`, `Jac.addAff` and `Jac.add` are straight-line programs over products,
squares and linear combinations. A linear combination is not reduced after each addition or
subtraction: it is emitted as one expression per limb, with a multiple of `2 p` added so that no
limb goes negative, and reduced once (`Fp.carry`) when it is stored, or earlier when a product would
otherwise overflow. The generator tracks the largest value every limb can take (a bound vector per
value, starting from `Fp.carry`'s own bounds for inputs) and refuses to emit code in which a
product operand exceeds `2^29` per limb, a column or a fold exceeds `2^62`, or a limb expression
could wrap, so the bounds in the generated file hold for every input of reduced limbs.

Usage: scripts/gen_point_ops.py > NearCrypto/Secp256k1/PointOps.lean; then `just lean-format` on
the file.
"""

M = 1 << 26
P_LIMBS = [0x3FFFC2F, 0x3FFFFBF] + [0x3FFFFFF] * 7 + [0x3FFFFF]
TWO_P = [2 * x for x in P_LIMBS]
LIMIT = 1 << 62
OPERAND = 1 << 29


def sim_carry(b):
    """Largest limbs after `Fp.carry` of limbs bounded by `b` (and the check that nothing wraps)."""
    r = list(b)
    assert all(x < LIMIT for x in r), r
    for i in range(9):
        c = r[i] >> 26
        r[i] = min(r[i], M - 1)
        r[i + 1] += c
    c = r[9] >> 22
    r[9] = min(r[9], (1 << 22) - 1)
    r[0] += 977 * c
    r[1] += c << 6
    c = r[0] >> 26
    r[0] = min(r[0], M - 1)
    r[1] += c
    c = r[1] >> 26
    out = [r[0], min(r[1], M - 1), r[2] + c] + r[3:]
    assert all(x < (1 << 63) for x in out)
    return out


REDUCED = sim_carry([LIMIT - 1] * 10)


def sim_mul(a, b):
    """Largest limbs of a product of operands bounded by `a` and `b`."""
    assert max(a) <= OPERAND and max(b) <= OPERAND, (max(a), max(b))
    c = [0] * 19
    for i in range(10):
        for j in range(10):
            c[i + j] += a[i] * b[j]
    h = []
    k = 0
    for m in range(9):
        x = c[10 + m] + k
        assert x < LIMIT
        h.append(min(x, M - 1))
        k = x >> 26
    h.append(k)
    r = [c[0] + 15632 * h[0] + 16007168 * h[9], c[1] + 15632 * h[1] + 1024 * h[0] + 1048576 * h[9]]
    r += [c[m] + 15632 * h[m] + 1024 * h[m - 1] for m in range(2, 10)]
    assert all(x < LIMIT for x in r), [x.bit_length() for x in r]
    return sim_carry(r)


class Form:
    """A linear combination `sum coef * value` of materialised values."""

    def __init__(self, terms):
        self.terms = {k: v for k, v in terms.items() if v != 0}

    def __add__(self, other):
        other = other if isinstance(other, Form) else NotImplemented
        t = dict(self.terms)
        for k, v in other.terms.items():
            t[k] = t.get(k, 0) + v
        return Form(t)

    def __sub__(self, other):
        return self + other * -1

    def __mul__(self, c):
        return Form({k: v * c for k, v in self.terms.items()})

    __rmul__ = __mul__


class Prog:
    def __init__(self, name, doc, params, result):
        self.name, self.doc, self.params, self.result = name, doc, params, result
        self.lines = []
        self.bounds = {}
        self.cache = {}
        self.count = 0

    def fresh(self, hint):
        self.count += 1
        return f"{hint}{self.count}"

    def input(self, lean, bound=None):
        self.bounds[lean] = list(bound or REDUCED)
        return Form({lean: 1})

    def limb_exprs(self, f):
        """The per-limb Lean expressions, the offset used and the bound vector of a form."""
        pos = {k: v for k, v in f.terms.items() if v > 0}
        neg = {k: -v for k, v in f.terms.items() if v < 0}
        need = [sum(c * self.bounds[k][i] for k, c in neg.items()) for i in range(10)]
        k2p = 0
        while any(k2p * TWO_P[i] < need[i] for i in range(10)):
            k2p += 1
        exprs, bound = [], []
        for i in range(10):
            parts = [f"{k}.l{i}" if c == 1 else f"{c} * {k}.l{i}" for k, c in pos.items()]
            if k2p:
                parts.append(f"{k2p * TWO_P[i]}")
            e = " + ".join(parts) if parts else "0"
            for k, c in neg.items():
                e += f" - {k}.l{i}" if c == 1 else f" - {c} * {k}.l{i}"
            exprs.append(e)
            bound.append(sum(c * self.bounds[k][i] for k, c in pos.items()) + k2p * TWO_P[i])
        assert all(b < LIMIT for b in bound)
        return exprs, bound

    def single(self, f):
        if len(f.terms) == 1:
            (k, c), = f.terms.items()
            if c == 1:
                return k
        return None

    def operand(self, f, hint="t"):
        """A Lean variable holding the form, reduced first when its limbs are too large."""
        s = self.single(f)
        if s is not None:
            return s
        key = tuple(sorted(f.terms.items()))
        if key in self.cache:
            return self.cache[key]
        exprs, bound = self.limb_exprs(f)
        name = self.fresh(hint)
        if max(bound) <= OPERAND:
            self.lines.append(f"  let {name} : Fp := ⟨{', '.join(exprs)}⟩")
            self.bounds[name] = bound
        else:
            self.lines.append(f"  let {name} := Fp.carry {' '.join('(' + e + ')' for e in exprs)}")
            self.bounds[name] = sim_carry(bound)
        self.cache[key] = name
        return name

    def product(self, a, b, hint="p"):
        x, y = self.operand(a), self.operand(b)
        name = self.fresh(hint)
        if x == y:
            self.lines.append(f"  let {name} := Fp.sq {x}")
            self.bounds[name] = sim_mul(self.bounds[x], self.bounds[x])
        else:
            self.lines.append(f"  let {name} := Fp.mul {x} {y}")
            self.bounds[name] = sim_mul(self.bounds[x], self.bounds[y])
        assert all(u <= r for u, r in zip(self.bounds[name], REDUCED))
        return Form({name: 1})

    def reduced(self, f, hint="o"):
        """A form materialised with `Fp.carry`: a stored result, at most `REDUCED` per limb."""
        s = self.single(f)
        if s is not None and all(u <= r for u, r in zip(self.bounds[s], REDUCED)):
            return Form({s: 1})
        exprs, bound = self.limb_exprs(f)
        name = self.fresh(hint)
        self.lines.append(f"  let {name} := Fp.carry {' '.join('(' + e + ')' for e in exprs)}")
        self.bounds[name] = sim_carry(bound)
        assert all(u <= r for u, r in zip(self.bounds[name], REDUCED))
        return Form({name: 1})

    def emit(self):
        params = " ".join(f"({p} : {t})" for p, t in self.params)
        out = [f"/-- {self.doc} -/", f"def {self.name} {params} : {self.result[0]} :="]
        out += self.lines
        out.append(f"  {self.result[1]}")
        return "\n".join(out)


def name_of(f):
    (k, _), = f.terms.items()
    return k


def dbl():
    p = Prog("dblCore", "The coordinates of `2 (X : Y : Z)` (`dbl-2009-l`).",
             [("X", "Fp"), ("Y", "Fp"), ("Z", "Fp")], ("Jac", ""))
    X, Y, Z = (p.input(n) for n in "XYZ")
    A = p.product(X, X, "a")
    B = p.product(Y, Y, "b")
    C = p.product(B, B, "c")
    T = p.product(X + B, X + B, "t")
    D = (T - A - C) * 2
    E = A * 3
    F = p.product(E, E, "f")
    X3 = p.reduced(F - D * 2, "x")
    Y3 = p.reduced(p.product(E, D - X3, "m") - C * 8, "y")
    Z3 = p.reduced(p.product(Y * 2, Z, "z"), "z")
    p.result = ("Jac", f"⟨{name_of(X3)}, {name_of(Y3)}, {name_of(Z3)}, false⟩")
    return p


def add_aff_pre():
    p = Prog("addAffPre", "`Z₁²`, `H` and `R₀` of the mixed addition of an affine `(qx, qy)` to `(X : Y : Z)`.",
             [("X", "Fp"), ("Y", "Fp"), ("Z", "Fp"), ("qx", "Fp"), ("qy", "Fp")], ("Fp × Fp × Fp", ""))
    X, Y, Z, qx, qy = (p.input(n) for n in ["X", "Y", "Z", "qx", "qy"])
    z1z1 = p.reduced(p.product(Z, Z, "z"), "zz")
    u2 = p.product(qx, z1z1, "u")
    h = p.reduced(u2 - X, "h")
    s2 = p.product(p.product(qy, Z, "s"), z1z1, "s")
    r0 = p.reduced(s2 - Y, "r")
    p.result = ("Fp × Fp × Fp", f"({name_of(z1z1)}, {name_of(h)}, {name_of(r0)})")
    return p


def add_aff_post():
    p = Prog("addAffPost", "The sum of `(X : Y : Z)` and an affine point, from `Z₁²`, `H` and `R₀`.",
             [("X", "Fp"), ("Y", "Fp"), ("Z", "Fp"), ("z1z1", "Fp"), ("h", "Fp"), ("r0", "Fp")], ("Jac", ""))
    X, Y, Z, z1z1, h, r0 = (p.input(n) for n in ["X", "Y", "Z", "z1z1", "h", "r0"])
    hh = p.product(h, h, "hh")
    i = hh * 4
    j = p.product(h, i, "j")
    r = r0 * 2
    v = p.product(X, i, "v")
    sr = p.product(r, r, "sr")
    X3 = p.reduced(sr - j - v * 2, "x")
    Y3 = p.reduced(p.product(r, v - X3, "m") - p.product(Y, j, "yj") * 2, "y")
    Z3 = p.reduced(p.product(Z + h, Z + h, "zh") - z1z1 - hh, "z")
    p.result = ("Jac", f"⟨{name_of(X3)}, {name_of(Y3)}, {name_of(Z3)}, false⟩")
    return p


def add_pre():
    p = Prog("addPre", "`Z₁²`, `Z₂²`, `U₁`, `S₁`, `H` and `R₀` of the addition of `(X1 : Y1 : Z1)` and `(X2 : Y2 : Z2)`.",
             [("X1", "Fp"), ("Y1", "Fp"), ("Z1", "Fp"), ("X2", "Fp"), ("Y2", "Fp"), ("Z2", "Fp")],
             ("Fp × Fp × Fp × Fp × Fp × Fp", ""))
    X1, Y1, Z1, X2, Y2, Z2 = (p.input(n) for n in ["X1", "Y1", "Z1", "X2", "Y2", "Z2"])
    z1z1 = p.reduced(p.product(Z1, Z1, "z"), "zz")
    z2z2 = p.reduced(p.product(Z2, Z2, "z"), "zz")
    u1 = p.reduced(p.product(X1, z2z2, "u"), "uu")
    u2 = p.product(X2, z1z1, "u")
    h = p.reduced(u2 - u1, "h")
    s1 = p.reduced(p.product(p.product(Y1, Z2, "s"), z2z2, "s"), "ss")
    s2 = p.product(p.product(Y2, Z1, "s"), z1z1, "s")
    r0 = p.reduced(s2 - s1, "r")
    names = ", ".join(name_of(f) for f in [z1z1, z2z2, u1, s1, h, r0])
    p.result = ("Fp × Fp × Fp × Fp × Fp × Fp", f"({names})")
    return p


def add_post():
    p = Prog("addPost", "The sum of `(X1 : Y1 : Z1)` and `(X2 : Y2 : Z2)` from the values of `addPre`.",
             [("Z1", "Fp"), ("Z2", "Fp"), ("z1z1", "Fp"), ("z2z2", "Fp"), ("u1", "Fp"), ("s1", "Fp"),
              ("h", "Fp"), ("r0", "Fp")], ("Jac", ""))
    Z1, Z2, z1z1, z2z2, u1, s1, h, r0 = (p.input(n) for n in
                                           ["Z1", "Z2", "z1z1", "z2z2", "u1", "s1", "h", "r0"])
    i = p.product(h * 2, h * 2, "i")
    j = p.product(h, i, "j")
    r = r0 * 2
    v = p.product(u1, i, "v")
    sr = p.product(r, r, "sr")
    X3 = p.reduced(sr - j - v * 2, "x")
    Y3 = p.reduced(p.product(r, v - X3, "m") - p.product(s1, j, "sj") * 2, "y")
    zs = p.product(Z1 + Z2, Z1 + Z2, "zs")
    Z3 = p.reduced(p.product(zs - z1z1 - z2z2, h, "z"), "z")
    p.result = ("Jac", f"⟨{name_of(X3)}, {name_of(Y3)}, {name_of(Z3)}, false⟩")
    return p


print("""import NearCrypto.Secp256k1.Point

/-!
# Point arithmetic with lazy reduction

Generated by `scripts/gen_point_ops.py`; see there for the construction and the bounds. Inputs
are reduced field elements (`Fp`).
-/

namespace NearCrypto.Secp256k1

open Fp
""")
for prog in [dbl(), add_aff_pre(), add_aff_post(), add_pre(), add_post()]:
    print(prog.emit())
    print()
print("end NearCrypto.Secp256k1")
