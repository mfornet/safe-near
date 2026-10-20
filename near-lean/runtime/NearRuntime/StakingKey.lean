import NearRuntime.Types

namespace Near.StakingKey

/-- Curve25519 base field. Compressed Edwards encoding uses its low 255 bits. -/
def prime : Nat := 2 ^ 255 - 19

/-- Edwards25519 parameter `-121665/121666` in the base field. -/
def edwardsD : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The nonnegative square root of -1 used by dalek's square-root ratio. -/
def sqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- Prime-order subgroup order. -/
def groupOrder : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

private def add (a b : Nat) : Nat := (a + b) % prime
private def sub (a b : Nat) : Nat := (a + prime - b % prime) % prime
private def mul (a b : Nat) : Nat := a * b % prime
private def neg (a : Nat) : Nat := sub 0 a

private def powLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, result => result
  | fuel + 1, base, exponent, result =>
    if exponent == 0 then result else
      powLoop fuel (mul base base) (exponent / 2)
        (if exponent % 2 == 1 then mul result base else result)

/-- All exponents used here fit in 256 bits; the loop has one step per bit. -/
private def pow (base exponent : Nat) : Nat := powLoop 256 base exponent 1

structure Point where
  x : Nat
  y : Nat
  z : Nat
  t : Nat

private def identity : Point := ⟨0, 1, 1, 0⟩

/-- Complete extended-coordinate addition for twisted Edwards a=-1. -/
private def pointAdd (left right : Point) : Point :=
  let a := mul (sub left.y left.x) (sub right.y right.x)
  let b := mul (add left.y left.x) (add right.y right.x)
  let c := mul (mul left.t right.t) (add edwardsD edwardsD)
  let d := mul (add left.z left.z) right.z
  let e := sub b a
  let f := sub d c
  let g := add d c
  let h := add b a
  ⟨mul e f, mul g h, mul f g, mul e h⟩

private def scalarLoop : Nat → Nat → Point → Point → Point
  | 0, _, _, result => result
  | fuel + 1, scalar, point, result =>
    if scalar == 0 then result else
      scalarLoop fuel (scalar / 2) (pointAdd point point)
        (if scalar % 2 == 1 then pointAdd result point else result)

private def littleEndian (bytes : List UInt8) : Nat :=
  bytes.foldr (fun byte result => byte.toNat + 256 * result) 0

/-- Dalek accepts noncanonical y encodings by reducing the masked field value.
The sign bit chooses x after selecting the nonnegative square root. -/
def decompress (bytes : List UInt8) : Option Point := do
  if bytes.length != 32 then none else
  let encoded := littleEndian bytes
  let y := (encoded % (2 ^ 255)) % prime
  let sign := encoded / (2 ^ 255)
  let yy := mul y y
  let u := sub yy 1
  let v := add (mul edwardsD yy) 1
  let v3 := mul (mul v v) v
  let v7 := mul (mul v3 v3) v
  let root := mul (mul u v3) (pow (mul u v7) ((prime - 5) / 8))
  let check := mul v (mul root root)
  if check != u && check != neg u then none else
  let root := if check == neg u then mul root sqrtM1 else root
  let root := if root % 2 == 1 then neg root else root
  let x := if sign == 1 then neg root else root
  return ⟨x, y, 1, mul x y⟩

/-- Native `EdwardsPoint::is_torsion_free` checks multiplication by the subgroup
order, including the identity. On-curve membership alone is insufficient. -/
def torsionFree (point : Point) : Bool :=
  let result := scalarLoop 256 groupOrder point identity
  result.x == 0 && result.y == result.z && result.z != 0

/-- Pinned nearcore `near_crypto::key_conversion::is_valid_staking_key` predicate
for decoded ordinary key encodings. Non-Ed25519 keys are unsuitable. -/
def suitable (key : PublicKey) : Bool :=
  match key with
  | 0 :: bytes => match decompress bytes with
    | none => false
    | some point => torsionFree point
  | _ => false

theorem edwardsD_relation : (edwardsD * 121666) % prime = prime - 121665 := by decide

theorem sqrtM1_square : (sqrtM1 * sqrtM1) % prime = prime - 1 := by decide

end Near.StakingKey
