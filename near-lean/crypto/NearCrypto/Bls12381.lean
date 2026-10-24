import NearCrypto.Bls12381.HashToCurve

/-!
# BLS12-381: the VM's host functions

The nine `bls12381_*` host functions exactly as `near-vm-runner` 0.37.4 runs them
(`logic/bls12381.rs`, over `blst` 0.3.11):

* **Points** are the uncompressed ZCash serialization: `G1` is `x ‖ y`, 96 bytes of big-endian
  field elements, and `G2` is `x.c1 ‖ x.c0 ‖ y.c1 ‖ y.c0`, 192 bytes. The first byte holds three
  flags in its top bits (`0x80` compressed, `0x40` infinity, `0x20` sign). The host functions
  reject `0x80` on uncompressed input; `blst_p1_deserialize` then takes a point with no flag as
  two field elements below `p` that satisfy the curve equation (no subgroup check), the infinity
  as the exact bytes `0x40 0 … 0`, and everything else as a bad encoding. Infinity is written as
  the same exact bytes.
* **NEP-488** (`bls12381_not_in_group_fix`): the points of `E(Fp)` with abscissa zero, `(0, ±2)`,
  have order 3 and `blst` reports them as `BLST_POINT_NOT_IN_GROUP` after decoding them. With the fix
  (`version = 1`) they are accepted by `p1_sum` and `p1_decompress`; without it (`version = 0`,
  protocol 86) they are errors. `G2` has no such case.
* **Return values**: a function returns 0 and writes its result, or returns 1 for an invalid
  point, sign or field element (`none` below); a length that is not a multiple of the item size is
  an error of the VM. The pairing check returns 0 (product is one), 1 (an invalid point or one
  outside `G1` / `G2`) or 2.
* **`p1_sum`, `p2_sum`**: `(sign, point)` items, 97 / 193 bytes, sign 0 or 1; the points only have
  to be on the curve. **`g1_multiexp`, `g2_multiexp`**: `(point, scalar)` items, the point in the
  prime-order group, the scalar 32 little-endian bytes (any value). **`p1_decompress`,
  `p2_decompress`**: 48 / 96-byte compressed points (the flag `0x80` required) to 96 / 192 bytes;
  an abscissa below `p` with a root, the sign flag choosing the larger or the smaller `y`, no
  subgroup check. **`map_fp_to_g1`, `map_fp2_to_g2`**: canonical field elements to points of the
  groups. **`pairing_check`**: `(G1, G2)` items of 288 bytes.

`Spec` is built on the reference group laws, pairing and cofactor clearing; `Impl` on the fast
ones and on `blst`'s own subgroup tests.
-/

namespace NearCrypto.Bls12381

open NearCrypto.Pairing

/-- The operations of one of the two groups the host functions are built from. -/
structure Side (α : Type) where
  /-- Bytes of an uncompressed point. -/
  size : Nat
  /-- Bytes of a compressed point, and of the field element mapped to the group. -/
  comp : Nat
  /-- `∑ ± Pᵢ` over the curve (the flag negates). -/
  sum : List (Bool × α) → α
  /-- Whether a point of the curve is in the prime-order group. -/
  inGroup : α → Bool
  /-- `∑ kᵢ Pᵢ` for points of the group. -/
  multiexp : List (α × Nat) → α
  /-- Deserialization with the NEP-488 version, `none` for an error. -/
  parse : Nat → ByteArray → Nat → Option α
  /-- `blst_p_uncompress` for a flagged compressed point. -/
  uncompress : Nat → ByteArray → Nat → Option α
  /-- The serialization. -/
  serialize : α → ByteArray
  /-- The canonical field element at an offset mapped to the group. -/
  mapTo : ByteArray → Nat → Option α

/-- The operations of the host functions of both groups and the pairing. -/
structure Ops where
  g1 : Side G1
  g2 : Side G2
  /-- Whether `∏ e(Pᵢ, Qᵢ) = 1` for points of the groups. -/
  pairingCheck : List (G1 × G2) → Bool

/-! ### Encodings -/

/-- Whether the bytes `off + 1` to `off + n - 1` are zero. -/
def zeroTail (b : ByteArray) (off n : Nat) : Bool :=
  (List.range (n - 1)).all fun i => b.get! (off + 1 + i) == 0

/-- A canonical field element: 48 big-endian bytes below `p`. -/
def decodeFp (b : ByteArray) (off : Nat) : Option Nat :=
  let v := beNat b off 48
  if v < p then some v else none

def curveRhs (x : Nat) : Nat :=
  (x * x % p * x + 4) % p

def curveRhs2 (x : Fp2) : Fp2 :=
  Fp2.add p (Fp2.mul p (Fp2.sqr p x) x) ⟨4, 4⟩

def serializeG1 : G1 → ByteArray
  | none => (zeros 96).set! 0 0x40
  | some (x, y) => toBe x 48 ++ toBe y 48

def serializeG2 : G2 → ByteArray
  | none => (zeros 192).set! 0 0x40
  | some (x, y) => toBe x.c1 48 ++ toBe x.c0 48 ++ toBe y.c1 48 ++ toBe y.c0 48

/-- Whether a field element is "large" for the sign flag: above `(p - 1) / 2`. -/
def largeFp (y : Nat) : Bool :=
  2 * y > p

/-- The same for `Fp2`: the imaginary part decides unless it is zero. -/
def largeFp2 (y : Fp2) : Bool :=
  if y.c1 != 0 then largeFp y.c1 else largeFp y.c0

/-- The compressed form of a point of `G1`: the abscissa with the flags `0x80` and, for the larger
ordinate, `0x20` (infinity: `0xc0` and zeros). -/
def compressG1 : G1 → ByteArray
  | none => (zeros 48).set! 0 0xc0
  | some (x, y) =>
    let b := toBe x 48
    b.set! 0 (b.get! 0 ||| 0x80 ||| if largeFp y then 0x20 else 0)

def compressG2 : G2 → ByteArray
  | none => (zeros 96).set! 0 0xc0
  | some (x, y) =>
    let b := toBe x.c1 48 ++ toBe x.c0 48
    b.set! 0 (b.get! 0 ||| 0x80 ||| if largeFp2 y then 0x20 else 0)

/-- `blst_p1_deserialize` for a 96-byte item without the compressed flag, `parse_p1`: `version = 0`
also rejects `(0, ±2)`. The infinity is `some none`. -/
def parseG1 (version : Nat) (b : ByteArray) (off : Nat) : Option G1 :=
  let in0 := b.get! off
  if in0 &&& 0x80 != 0 then none
  else
    if in0 &&& 0xe0 == 0 then
      let x := beNat b off 48
      let y := beNat b (off + 48) 48
      if x < p && y < p && y * y % p == curveRhs x && (x != 0 || version != 0) then
        some (some (x, y))
      else none
    else if in0 == 0x40 && zeroTail b off 96 then some none else none

def parseG2 (_version : Nat) (b : ByteArray) (off : Nat) : Option G2 :=
  let in0 := b.get! off
  if in0 &&& 0x80 != 0 then none
  else
    if in0 &&& 0xe0 == 0 then
      match decodeFp b off, decodeFp b (off + 48), decodeFp b (off + 96),
        decodeFp b (off + 144) with
      | some x1, some x0, some y1, some y0 =>
        let x : Fp2 := ⟨x0, x1⟩
        let y : Fp2 := ⟨y0, y1⟩
        if Fp2.sqr p y == curveRhs2 x then some (some (x, y)) else none
      | _, _, _, _ => none
    else if in0 == 0x40 && zeroTail b off 192 then some none else none

/-- `blst_p1_uncompress` of the 48 bytes at `off`, whose compressed flag is set. -/
def uncompressG1 (version : Nat) (b : ByteArray) (off : Nat) : Option G1 :=
  let in0 := b.get! off
  if in0 &&& 0x40 != 0 then if in0 &&& 0x3f == 0 && zeroTail b off 48 then some none else none
  else
    let x := beNat b off 48 &&& (2 ^ 381 - 1)
    if x ≥ p then none
    else
      match sqrtMod p (curveRhs x) with
      | none => none
      | some y =>
        let y := if largeFp y == (in0 &&& 0x20 != 0) then y else p - y
        if x == 0 && version == 0 then none else some (some (x, y))

def uncompressG2 (_version : Nat) (b : ByteArray) (off : Nat) : Option G2 :=
  let in0 := b.get! off
  if in0 &&& 0x40 != 0 then if in0 &&& 0x3f == 0 && zeroTail b off 96 then some none else none
  else
    let x1 := beNat b off 48 &&& (2 ^ 381 - 1)
    let x0 := beNat b (off + 48) 48
    if x1 ≥ p || x0 ≥ p then none
    else
      let x : Fp2 := ⟨x0, x1⟩
      match Fp2.sqrt p (curveRhs2 x) with
      | none => none
      | some y =>
        let y := if largeFp2 y == (in0 &&& 0x20 != 0) then y else Fp2.neg p y
        some (some (x, y))

/-! ### Host functions -/

section Host

variable {α : Type} (S : Side α)

/-- The error of a length that is not a multiple of the item size. -/
def checkSize (data : ByteArray) (item : Nat) : Except String Unit :=
  if data.size % item != 0 then throw s!"{data.size} is not divisible by {item}" else pure ()

/-- `bls12381_p1_sum` / `bls12381_p2_sum`: `none` is the return value 1. -/
def pSum (version : Nat) (data : ByteArray) : Except String (Option ByteArray) := do
  checkSize data (1 + S.size)
  let mut terms := #[]
  for i in [0:data.size / (1 + S.size)] do
    let off := i * (1 + S.size)
    let some pt := S.parse version data (off + 1) | return none
    match data.get! off with
    | 0 =>
      terms := terms.push (false, pt)
    | 1 =>
      terms := terms.push (true, pt)
    | _ =>
      return none
  pure (some (S.serialize (S.sum terms.toList)))

/-- `bls12381_g1_multiexp` / `bls12381_g2_multiexp`. -/
def gMultiexp (version : Nat) (data : ByteArray) : Except String (Option ByteArray) := do
  checkSize data (S.size + 32)
  let mut terms := #[]
  for i in [0:data.size / (S.size + 32)] do
    let off := i * (S.size + 32)
    let some pt := S.parse version data off | return none
    if !S.inGroup pt then
      return none
    terms := terms.push (pt, leNat data (off + S.size) 32)
  pure (some (S.serialize (S.multiexp terms.toList)))

/-- `bls12381_p1_decompress` / `bls12381_p2_decompress`. -/
def pDecompress (version : Nat) (data : ByteArray) : Except String (Option ByteArray) := do
  checkSize data S.comp
  let mut out := ByteArray.empty
  for i in [0:data.size / S.comp] do
    let off := i * S.comp
    if data.get! off &&& 0x80 == 0 then
      return none
    let some pt := S.uncompress version data off | return none
    out := out ++ S.serialize pt
  pure (some out)

/-- `bls12381_map_fp_to_g1` / `bls12381_map_fp2_to_g2`. -/
def mapToG (data : ByteArray) : Except String (Option ByteArray) := do
  checkSize data S.comp
  let mut out := ByteArray.empty
  for i in [0:data.size / S.comp] do
    let some pt := S.mapTo data (i * S.comp) | return none
    out := out ++ S.serialize pt
  pure (some out)

end Host

section Wrappers

variable (ops : Ops)

def p1Sum :=
  pSum ops.g1

def p2Sum :=
  pSum ops.g2

def g1Multiexp :=
  gMultiexp ops.g1

def g2Multiexp :=
  gMultiexp ops.g2

def p1Decompress :=
  pDecompress ops.g1

def p2Decompress :=
  pDecompress ops.g2

def mapFpToG1 :=
  mapToG ops.g1

def mapFp2ToG2 :=
  mapToG ops.g2

/-- `bls12381_pairing_check`: 0, 1 or 2. -/
def pairingCheck (data : ByteArray) : Except String Nat := do
  checkSize data 288
  let mut pairs := #[]
  for i in [0:data.size / 288] do
    let off := i * 288
    let some a := parseG1 0 data off | return 1
    -- `blst_p1_deserialize` must succeed: the corner points of order 3 are errors here
    if !ops.g1.inGroup a then
      return 1
    let some q := parseG2 0 data (off + 96) | return 1
    if !ops.g2.inGroup q then
      return 1
    pairs := pairs.push (a, q)
  pure (if ops.pairingCheck pairs.toList then 0 else 2)

end Wrappers

/-! ### The reference operations -/

namespace Spec

def sum {α : Type} (F : Fld α) (terms : List (Bool × Option (α × α))) : Option (α × α) :=
  Jac.toAffine F <|
    terms.foldl
      (fun acc (neg, pt) =>
        let j := Jac.ofAffine F pt
        Jac.add F acc (if neg then Jac.neg F j else j))
      (Jac.inf F)

def multiexp {α : Type} (F : Fld α) (terms : List (Option (α × α) × Nat)) : Option (α × α) :=
  Jac.toAffine F <|
    terms.foldl (fun acc (pt, k) => Jac.add F acc (Jac.mul F (Jac.ofAffine F pt) k)) (Jac.inf F)

/-- A point of the curve is in the group of order `r` when `[r] P = O`. -/
def inGroup {α : Type} (F : Fld α) (pt : Option (α × α)) : Bool :=
  Jac.isInf F (Jac.mul F (Jac.ofAffine F pt) r)

def mapTo1 (b : ByteArray) (off : Nat) : Option G1 :=
  (decodeFp b off).map fun u => HashToCurve.clear1 (HashToCurve.mapToE1 u)

def mapTo2 (b : ByteArray) (off : Nat) : Option G2 := do
  let c1 ← decodeFp b off
  let c0 ← decodeFp b (off + 48)
  pure (HashToCurve.clear2Spec (HashToCurve.mapToE2 ⟨c0, c1⟩))

def g1 : Side G1 :=
  { size := 96, comp := 48, sum := sum f1, inGroup := inGroup f1, multiexp := multiexp f1,
    parse := parseG1, uncompress := uncompressG1, serialize := serializeG1, mapTo := mapTo1 }

def g2 : Side G2 :=
  { size := 192, comp := 96, sum := sum f2, inGroup := inGroup f2, multiexp := multiexp f2,
    parse := parseG2, uncompress := uncompressG2, serialize := serializeG2, mapTo := mapTo2 }

/-- The reference operations. -/
def ops : Ops :=
  { g1, g2, pairingCheck := Pairing.Spec.pairingCheck curve }

end Spec

/-! ### The fast operations -/

namespace Impl

/-- `P ∈ G1` by `blst`'s test (Scott, ePrint 2021/1130): `σ²(P) = -[z²] P` for
`σ(x, y) = (β x, y)`. The kernel of `σ² + z²` has `σ³ + z² (σ² + σ) + z⁴ = r` points, so on the
curve this is exactly the group of order `r`. -/
def inG1 : G1 → Bool
  | none => true
  | some (x, y) =>
    let q := Jac.mul f1 (Jac.ofAffine f1 (some (x, y))) (z * z)
    Jac.eqAffine f1 q (beta * beta % p * x % p) ((p - y) % p)

/-- `P ∈ G2` by `blst`'s test (Scott): `ψ(P) = [z] P` with `z` negative. -/
def inG2 : G2 → Bool
  | none => true
  | some (x, y) =>
    let q := Jac.mul f2 (Jac.ofAffine f2 (some (x, y))) z
    let psi := HashToCurve.psi (Jac.ofAffine f2 (some (x, y)))
    match Jac.toAffine f2 psi with
    | some (px, py) => Jac.eqAffine f2 q px (Fp2.neg p py)
    | none => false

def multiexp {α : Type} (F : Fld α) (terms : List (Option (α × α) × Nat)) : Option (α × α) :=
  Jac.toAffine F <| Jac.multiScalar F (terms.toArray.map fun (pt, k) => (Jac.ofAffine F pt, k))

def mapTo2 (b : ByteArray) (off : Nat) : Option G2 := do
  let c1 ← decodeFp b off
  let c0 ← decodeFp b (off + 48)
  pure (HashToCurve.clear2Impl (HashToCurve.mapToE2 ⟨c0, c1⟩))

def g1 : Side G1 :=
  { Spec.g1 with
    inGroup := inG1, multiexp := multiexp f1 }

def g2 : Side G2 :=
  { Spec.g2 with
    inGroup := inG2, multiexp := multiexp f2, mapTo := mapTo2 }

def pairingCheck (pairs : List (G1 × G2)) : Bool :=
  Pairing.Impl.pairingCheck params pairs

/-- The fast operations. -/
def ops : Ops :=
  { g1, g2, pairingCheck }

end Impl

end NearCrypto.Bls12381
