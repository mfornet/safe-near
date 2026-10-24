import NearCrypto.Pairing.Fp2

/-!
# Short Weierstrass groups `y² = x³ + b` in Jacobian coordinates

One implementation for `E(Fp)` and the twist over `Fp2`, over a record of field operations. A point is
`(X : Y : Z)` for the affine `(X / Z², Y / Z³)`, and `Z = 0` is the point at infinity. The
formulas are `dbl-2009-l` and `add-2007-bl` with the special cases of equal and opposite points.
-/

namespace NearCrypto.Pairing

/-- The operations of a field the group laws need. -/
structure Fld (α : Type) where
  zero : α
  one : α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  neg : α → α
  inv : α → α
  isZero : α → Bool
  eq : α → α → Bool
  /-- The coefficient `a` of `y² = x³ + a x + b`; zero for the curves with `j = 0`. -/
  a : α

/-- The field `Fp` as a record. -/
def fpFld (p : Nat) : Fld Nat :=
  { zero := 0, one := 1, add := Fp2.addMod p, sub := Fp2.subMod p, mul := fun a b => a * b % p,
    neg := Fp2.subMod p 0, inv := invMod p, isZero := (· == 0), eq := (· == ·), a := 0 }

/-- The field `Fp2` as a record. -/
def fp2Fld (p : Nat) : Fld Fp2 :=
  { zero := Fp2.zero, one := Fp2.one, add := Fp2.add p, sub := Fp2.sub p, mul := Fp2.mul p,
    neg := Fp2.neg p, inv := Fp2.inv p, isZero := Fp2.isZero, eq := (· == ·), a := Fp2.zero }

/-- A Jacobian point. -/
structure Jac (α : Type) where
  x : α
  y : α
  z : α

namespace Jac

variable {α : Type}

/-- The point at infinity. -/
def inf (F : Fld α) : Jac α :=
  ⟨F.one, F.one, F.zero⟩

def isInf (F : Fld α) (P : Jac α) : Bool :=
  F.isZero P.z

/-- The Jacobian form of an affine point (`none` is infinity). -/
def ofAffine (F : Fld α) : Option (α × α) → Jac α
  | none => inf F
  | some (x, y) => ⟨x, y, F.one⟩

/-- The affine form: one inversion. -/
def toAffine (F : Fld α) (P : Jac α) : Option (α × α) :=
  if F.isZero P.z then none
  else
    let zi := F.inv P.z
    let zi2 := F.mul zi zi
    some (F.mul P.x zi2, F.mul P.y (F.mul zi2 zi))

def neg (F : Fld α) (P : Jac α) : Jac α :=
  ⟨P.x, F.neg P.y, P.z⟩

/-- Doubling (`dbl-2009-l`; with `a ≠ 0` the slope numerator gains `a Z⁴`, as in `dbl-2007-bl`). -/
def dbl (F : Fld α) (P : Jac α) : Jac α :=
  if F.isZero P.z || F.isZero P.y then inf F
  else
    let a := F.mul P.x P.x
    let b := F.mul P.y P.y
    let c := F.mul b b
    let t := F.add P.x b
    let d := F.sub (F.sub (F.mul t t) a) c
    let d := F.add d d
    let e := F.add (F.add a a) a
    let e :=
      if F.isZero F.a then e
      else
        let zz := F.mul P.z P.z
        F.add e (F.mul F.a (F.mul zz zz))
    let f := F.mul e e
    let x3 := F.sub f (F.add d d)
    let c8 := F.add c c
    let c8 := F.add c8 c8
    let c8 := F.add c8 c8
    let y3 := F.sub (F.mul e (F.sub d x3)) c8
    let z3 := F.mul (F.add P.y P.y) P.z
    ⟨x3, y3, z3⟩

/-- Addition (`add-2007-bl`) with the special cases. -/
def add (F : Fld α) (P Q : Jac α) : Jac α :=
  if F.isZero P.z then Q
  else
    if F.isZero Q.z then P
    else
      let z1z1 := F.mul P.z P.z
      let z2z2 := F.mul Q.z Q.z
      let u1 := F.mul P.x z2z2
      let u2 := F.mul Q.x z1z1
      let s1 := F.mul (F.mul P.y Q.z) z2z2
      let s2 := F.mul (F.mul Q.y P.z) z1z1
      if F.eq u1 u2 then if F.eq s1 s2 then dbl F P else inf F
      else
        let h := F.sub u2 u1
        let i := F.add h h
        let i := F.mul i i
        let j := F.mul h i
        let r := F.sub s2 s1
        let r := F.add r r
        let v := F.mul u1 i
        let x3 := F.sub (F.sub (F.mul r r) j) (F.add v v)
        let sj := F.mul s1 j
        let y3 := F.sub (F.mul r (F.sub v x3)) (F.add sj sj)
        let zz := F.add P.z Q.z
        let z3 := F.mul (F.sub (F.sub (F.mul zz zz) z1z1) z2z2) h
        ⟨x3, y3, z3⟩

/-- `k P` by double and add from the top bit. -/
def mul (F : Fld α) (P : Jac α) (k : Nat) : Jac α :=
  Id.run do
    let mut r := inf F
    for i in [0:k.log2 + 1] do
      r := dbl F r
      if k.testBit (k.log2 - i) then
        r := add F r P
    return r

/-- Whether the Jacobian `P` is the affine point `(x, y)`. -/
def eqAffine (F : Fld α) (P : Jac α) (x y : α) : Bool :=
  if F.isZero P.z then false
  else
    let z2 := F.mul P.z P.z
    F.eq P.x (F.mul x z2) && F.eq P.y (F.mul y (F.mul z2 P.z))

/-! ### Several scalars at once -/

/-- The width-`w` non-adjacent form of `k`, least significant term first: odd terms below
`2^(w-1)` in absolute value, at least `w - 1` zeros after each. -/
def wnaf (k : Nat) (w : Nat) : Array Int :=
  Id.run do
    let mut k : Int := k
    let mut out := #[]
    let m : Int := 2 ^ w
    while k > 0 do
      if k % 2 == 1 then
        let d := k % m
        let d := if d ≥ m / 2 then d - m else d
        out := out.push d
        k := k - d
      else
        out := out.push 0
      k := k / 2
    return out

/-- `∑ kᵢ Pᵢ` by one chain of doublings shared by all terms, each term added from a table of its
odd multiples `P, 3 P, …` (window `w`). -/
def multiScalar (F : Fld α) (terms : Array (Jac α × Nat)) (w : Nat := 4) : Jac α :=
  Id.run do
    let n := 1 <<< (w - 2)
    let mut tables : Array (Array (Jac α)) := #[]
    let mut forms : Array (Array Int) := #[]
    for (P, k) in terms do
      let P2 := dbl F P
      let mut t := #[P]
      for _ in [1:n] do
        t := t.push (add F (t.getD (t.size - 1) P) P2)
      tables := tables.push t
      forms := forms.push (wnaf k w)
    let top := forms.foldl (fun m d => max m d.size) 0
    let mut r := inf F
    for i in [0:top] do
      let pos := top - 1 - i
      r := dbl F r
      for j in [0:terms.size] do
        let d := (forms[j]!).getD pos 0
        if d > 0 then
          r := add F r ((tables.getD j #[]).getD ((d.toNat - 1) / 2) (inf F))
        else if d < 0 then
          r := add F r (neg F ((tables.getD j #[]).getD (((-d).toNat - 1) / 2) (inf F)))
    return r

end Jac

end NearCrypto.Pairing
