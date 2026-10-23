import Wasm.Value

/-!
# Numeric operations

Section 4.3 of the specification ("Numerics"). Integer operations are on
`UInt32` / `UInt64` and reduce in the kernel. Floating-point operations go
through Lean's `Float32` / `Float`, which call the C library; a NaN produced
by an arithmetic operation is replaced by the canonical NaN, as nearcore's
engine does, while bitwise operations (`abs`, `neg`, `copysign`) and
reinterpretations preserve payloads.
-/

namespace Wasm.Numeric

/-! ## Integers -/

def _root_.UInt32.toIntS (x : UInt32) : Int :=
  if x.toNat < 2 ^ 31 then x.toNat else (x.toNat : Int) - 2 ^ 32

def _root_.UInt64.toIntS (x : UInt64) : Int :=
  if x.toNat < 2 ^ 63 then x.toNat else (x.toNat : Int) - 2 ^ 64

def intToUInt32 (i : Int) : UInt32 := UInt32.ofNat (i % (2 ^ 32 : Int)).toNat
def intToUInt64 (i : Int) : UInt64 := UInt64.ofNat (i % (2 ^ 64 : Int)).toNat

def bool (b : Bool) : UInt32 := if b then 1 else 0

def clz (bits : Nat) (x : Nat) : Nat :=
  go bits
where
  go : Nat → Nat
    | 0 => bits
    | n + 1 => if x >>> n % 2 == 1 then bits - 1 - n else go n

def ctz (bits : Nat) (x : Nat) : Nat :=
  go 0
where
  go (i : Nat) : Nat :=
    if i < bits then (if x >>> i % 2 == 1 then i else go (i + 1)) else bits
  termination_by bits - i

def popcnt (bits : Nat) (x : Nat) : Nat :=
  (List.range bits).foldl (fun acc i => acc + x >>> i % 2) 0

/-- Sign-extend the low `from_` bits of a `bits`-bit value. -/
def signExtend (bits from_ : Nat) (x : Nat) : Nat :=
  let low := x % 2 ^ from_
  if low < 2 ^ (from_ - 1) then low else low + (2 ^ bits - 2 ^ from_)

def iunop32 : IUnOp → UInt32 → UInt32
  | .clz, x => UInt32.ofNat (clz 32 x.toNat)
  | .ctz, x => UInt32.ofNat (ctz 32 x.toNat)
  | .popcnt, x => UInt32.ofNat (popcnt 32 x.toNat)
  | .extend8_s, x => UInt32.ofNat (signExtend 32 8 x.toNat)
  | .extend16_s, x => UInt32.ofNat (signExtend 32 16 x.toNat)
  | .extend32_s, x => x

def iunop64 : IUnOp → UInt64 → UInt64
  | .clz, x => UInt64.ofNat (clz 64 x.toNat)
  | .ctz, x => UInt64.ofNat (ctz 64 x.toNat)
  | .popcnt, x => UInt64.ofNat (popcnt 64 x.toNat)
  | .extend8_s, x => UInt64.ofNat (signExtend 64 8 x.toNat)
  | .extend16_s, x => UInt64.ofNat (signExtend 64 16 x.toNat)
  | .extend32_s, x => UInt64.ofNat (signExtend 64 32 x.toNat)

def ibinop32 : IBinOp → UInt32 → UInt32 → Except Trap UInt32
  | .add, a, b => .ok (a + b)
  | .sub, a, b => .ok (a - b)
  | .mul, a, b => .ok (a * b)
  | .div_u, a, b => if b == 0 then .error .integerDivideByZero else .ok (a / b)
  | .rem_u, a, b => if b == 0 then .error .integerDivideByZero else .ok (a % b)
  | .div_s, a, b =>
    if b == 0 then .error .integerDivideByZero
    else if a == 0x80000000 && b == 0xFFFFFFFF then .error .integerOverflow
    else .ok (intToUInt32 (Int.tdiv a.toIntS b.toIntS))
  | .rem_s, a, b =>
    if b == 0 then .error .integerDivideByZero
    else .ok (intToUInt32 (Int.tmod a.toIntS b.toIntS))
  | .and, a, b => .ok (a &&& b)
  | .or, a, b => .ok (a ||| b)
  | .xor, a, b => .ok (a ^^^ b)
  | .shl, a, b => .ok (a <<< (b % 32))
  | .shr_u, a, b => .ok (a >>> (b % 32))
  | .shr_s, a, b => .ok (intToUInt32 (a.toIntS >>> (b % 32).toNat))
  | .rotl, a, b => let k := b % 32; .ok ((a <<< k) ||| (a >>> ((32 - k) % 32)))
  | .rotr, a, b => let k := b % 32; .ok ((a >>> k) ||| (a <<< ((32 - k) % 32)))

def ibinop64 : IBinOp → UInt64 → UInt64 → Except Trap UInt64
  | .add, a, b => .ok (a + b)
  | .sub, a, b => .ok (a - b)
  | .mul, a, b => .ok (a * b)
  | .div_u, a, b => if b == 0 then .error .integerDivideByZero else .ok (a / b)
  | .rem_u, a, b => if b == 0 then .error .integerDivideByZero else .ok (a % b)
  | .div_s, a, b =>
    if b == 0 then .error .integerDivideByZero
    else if a == 0x8000000000000000 && b == 0xFFFFFFFFFFFFFFFF then .error .integerOverflow
    else .ok (intToUInt64 (Int.tdiv a.toIntS b.toIntS))
  | .rem_s, a, b =>
    if b == 0 then .error .integerDivideByZero
    else .ok (intToUInt64 (Int.tmod a.toIntS b.toIntS))
  | .and, a, b => .ok (a &&& b)
  | .or, a, b => .ok (a ||| b)
  | .xor, a, b => .ok (a ^^^ b)
  | .shl, a, b => .ok (a <<< (b % 64))
  | .shr_u, a, b => .ok (a >>> (b % 64))
  | .shr_s, a, b => .ok (intToUInt64 (a.toIntS >>> (b % 64).toNat))
  | .rotl, a, b => let k := b % 64; .ok ((a <<< k) ||| (a >>> ((64 - k) % 64)))
  | .rotr, a, b => let k := b % 64; .ok ((a >>> k) ||| (a <<< ((64 - k) % 64)))

def irelop32 : IRelOp → UInt32 → UInt32 → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt_u, a, b => a < b
  | .gt_u, a, b => a > b
  | .le_u, a, b => a ≤ b
  | .ge_u, a, b => a ≥ b
  | .lt_s, a, b => a.toIntS < b.toIntS
  | .gt_s, a, b => a.toIntS > b.toIntS
  | .le_s, a, b => a.toIntS ≤ b.toIntS
  | .ge_s, a, b => a.toIntS ≥ b.toIntS

def irelop64 : IRelOp → UInt64 → UInt64 → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt_u, a, b => a < b
  | .gt_u, a, b => a > b
  | .le_u, a, b => a ≤ b
  | .ge_u, a, b => a ≥ b
  | .lt_s, a, b => a.toIntS < b.toIntS
  | .gt_s, a, b => a.toIntS > b.toIntS
  | .le_s, a, b => a.toIntS ≤ b.toIntS
  | .ge_s, a, b => a.toIntS ≥ b.toIntS

/-! ## Floats

Every operation below takes and returns bit patterns. -/

def canonicalNaN32 : UInt32 := 0x7FC00000
def canonicalNaN64 : UInt64 := 0x7FF8000000000000

/-- Replace a NaN result by the canonical NaN. -/
def canon32 (x : Float32) : UInt32 := if x.isNaN then canonicalNaN32 else x.toBits
def canon64 (x : Float) : UInt64 := if x.isNaN then canonicalNaN64 else x.toBits

def isNegZero32 (x : Float32) : Bool := x.toBits == 0x80000000
def isNegZero64 (x : Float) : Bool := x.toBits == 0x8000000000000000

def sign32 (bits : UInt32) : UInt32 := bits &&& 0x80000000
def sign64 (bits : UInt64) : UInt64 := bits &&& 0x8000000000000000

/-- Round to nearest, ties to even. `Float32.round` rounds ties away from
zero, so ties are handled explicitly. A result of zero keeps the sign of `x`. -/
def nearest32 (x : Float32) : Float32 :=
  if x.isNaN || x.isInf then x else
  let f := x.floor
  let d := x - f
  let r := if d < 0.5 then f else if d > 0.5 then f + 1 else
    if (f / 2).floor * 2 == f then f else f + 1
  if r == 0 then Float32.ofBits (sign32 x.toBits) else r

def nearest64 (x : Float) : Float :=
  if x.isNaN || x.isInf then x else
  let f := x.floor
  let d := x - f
  let r := if d < 0.5 then f else if d > 0.5 then f + 1 else
    if (f / 2).floor * 2 == f then f else f + 1
  if r == 0 then Float.ofBits (sign64 x.toBits) else r

def trunc32 (x : Float32) : Float32 := if x < 0 then x.ceil else x.floor
def trunc64 (x : Float) : Float := if x < 0 then x.ceil else x.floor

def funop32 : FUnOp → UInt32 → UInt32
  | .abs, b => b &&& 0x7FFFFFFF
  | .neg, b => b ^^^ 0x80000000
  | .ceil, b => canon32 (Float32.ofBits b).ceil
  | .floor, b => canon32 (Float32.ofBits b).floor
  | .trunc, b => canon32 (trunc32 (Float32.ofBits b))
  | .nearest, b => canon32 (nearest32 (Float32.ofBits b))
  | .sqrt, b => canon32 (Float32.ofBits b).sqrt

def funop64 : FUnOp → UInt64 → UInt64
  | .abs, b => b &&& 0x7FFFFFFFFFFFFFFF
  | .neg, b => b ^^^ 0x8000000000000000
  | .ceil, b => canon64 (Float.ofBits b).ceil
  | .floor, b => canon64 (Float.ofBits b).floor
  | .trunc, b => canon64 (trunc64 (Float.ofBits b))
  | .nearest, b => canon64 (nearest64 (Float.ofBits b))
  | .sqrt, b => canon64 (Float.ofBits b).sqrt

/-- `min` and `max` with the spec's zero and NaN rules. -/
def fmin32 (a b : Float32) : Float32 :=
  if a.isNaN || b.isNaN then Float32.ofBits canonicalNaN32
  else if a == b then (if isNegZero32 a then a else b)
  else if a < b then a else b

def fmax32 (a b : Float32) : Float32 :=
  if a.isNaN || b.isNaN then Float32.ofBits canonicalNaN32
  else if a == b then (if isNegZero32 a then b else a)
  else if a > b then a else b

def fmin64 (a b : Float) : Float :=
  if a.isNaN || b.isNaN then Float.ofBits canonicalNaN64
  else if a == b then (if isNegZero64 a then a else b)
  else if a < b then a else b

def fmax64 (a b : Float) : Float :=
  if a.isNaN || b.isNaN then Float.ofBits canonicalNaN64
  else if a == b then (if isNegZero64 a then b else a)
  else if a > b then a else b

def fbinop32 : FBinOp → UInt32 → UInt32 → UInt32
  | .add, a, b => canon32 (Float32.ofBits a + Float32.ofBits b)
  | .sub, a, b => canon32 (Float32.ofBits a - Float32.ofBits b)
  | .mul, a, b => canon32 (Float32.ofBits a * Float32.ofBits b)
  | .div, a, b => canon32 (Float32.ofBits a / Float32.ofBits b)
  | .min, a, b => canon32 (fmin32 (Float32.ofBits a) (Float32.ofBits b))
  | .max, a, b => canon32 (fmax32 (Float32.ofBits a) (Float32.ofBits b))
  | .copysign, a, b => (a &&& 0x7FFFFFFF) ||| sign32 b

def fbinop64 : FBinOp → UInt64 → UInt64 → UInt64
  | .add, a, b => canon64 (Float.ofBits a + Float.ofBits b)
  | .sub, a, b => canon64 (Float.ofBits a - Float.ofBits b)
  | .mul, a, b => canon64 (Float.ofBits a * Float.ofBits b)
  | .div, a, b => canon64 (Float.ofBits a / Float.ofBits b)
  | .min, a, b => canon64 (fmin64 (Float.ofBits a) (Float.ofBits b))
  | .max, a, b => canon64 (fmax64 (Float.ofBits a) (Float.ofBits b))
  | .copysign, a, b => (a &&& 0x7FFFFFFFFFFFFFFF) ||| sign64 b

def frelop32 : FRelOp → UInt32 → UInt32 → Bool
  | .eq, a, b => Float32.ofBits a == Float32.ofBits b
  | .ne, a, b => !(Float32.ofBits a == Float32.ofBits b)
  | .lt, a, b => Float32.ofBits a < Float32.ofBits b
  | .gt, a, b => Float32.ofBits a > Float32.ofBits b
  | .le, a, b => Float32.ofBits a ≤ Float32.ofBits b
  | .ge, a, b => Float32.ofBits a ≥ Float32.ofBits b

def frelop64 : FRelOp → UInt64 → UInt64 → Bool
  | .eq, a, b => Float.ofBits a == Float.ofBits b
  | .ne, a, b => !(Float.ofBits a == Float.ofBits b)
  | .lt, a, b => Float.ofBits a < Float.ofBits b
  | .gt, a, b => Float.ofBits a > Float.ofBits b
  | .le, a, b => Float.ofBits a ≤ Float.ofBits b
  | .ge, a, b => Float.ofBits a ≥ Float.ofBits b

/-! ## Conversions -/

/-- Trapping truncation: the float must be a number whose integral part is in
range. Lean's casts saturate, so the range is checked first. -/
def truncCheck32 (x : Float32) (lo hi : Float32) : Except Trap Unit :=
  if x.isNaN then .error .invalidConversionToInteger
  else if x > lo && x < hi then .ok () else .error .integerOverflow

def truncCheck64 (x : Float) (lo hi : Float) : Except Trap Unit :=
  if x.isNaN then .error .invalidConversionToInteger
  else if x > lo && x < hi then .ok () else .error .integerOverflow

def cvt (op : CvtOp) (v : Value) : Except Trap Value :=
  match op, v with
  | .i32_wrap_i64, .i64 x => .ok (.i32 x.toUInt32)
  | .i64_extend_i32_u, .i32 x => .ok (.i64 x.toUInt64)
  | .i64_extend_i32_s, .i32 x => .ok (.i64 (intToUInt64 x.toIntS))
  | .i32_trunc_f32_s, .f32 b => do
    let x := Float32.ofBits b
    truncCheck32 x (-2147483904.0) 2147483648.0
    return .i32 x.toInt32.toUInt32
  | .i32_trunc_f32_u, .f32 b => do
    let x := Float32.ofBits b
    truncCheck32 x (-1.0) 4294967296.0
    return .i32 x.toUInt32
  | .i32_trunc_f64_s, .f64 b => do
    let x := Float.ofBits b
    truncCheck64 x (-2147483649.0) 2147483648.0
    return .i32 x.toInt32.toUInt32
  | .i32_trunc_f64_u, .f64 b => do
    let x := Float.ofBits b
    truncCheck64 x (-1.0) 4294967296.0
    return .i32 x.toUInt32
  | .i64_trunc_f32_s, .f32 b => do
    let x := Float32.ofBits b
    truncCheck32 x (-9223373136366403584.0) 9223372036854775808.0
    return .i64 x.toInt64.toUInt64
  | .i64_trunc_f32_u, .f32 b => do
    let x := Float32.ofBits b
    truncCheck32 x (-1.0) 18446744073709551616.0
    return .i64 x.toUInt64
  | .i64_trunc_f64_s, .f64 b => do
    let x := Float.ofBits b
    truncCheck64 x (-9223372036854777856.0) 9223372036854775808.0
    return .i64 x.toInt64.toUInt64
  | .i64_trunc_f64_u, .f64 b => do
    let x := Float.ofBits b
    truncCheck64 x (-1.0) 18446744073709551616.0
    return .i64 x.toUInt64
  | .i32_trunc_sat_f32_s, .f32 b => .ok (.i32 (Float32.ofBits b).toInt32.toUInt32)
  | .i32_trunc_sat_f32_u, .f32 b => .ok (.i32 (Float32.ofBits b).toUInt32)
  | .i32_trunc_sat_f64_s, .f64 b => .ok (.i32 (Float.ofBits b).toInt32.toUInt32)
  | .i32_trunc_sat_f64_u, .f64 b => .ok (.i32 (Float.ofBits b).toUInt32)
  | .i64_trunc_sat_f32_s, .f32 b => .ok (.i64 (Float32.ofBits b).toInt64.toUInt64)
  | .i64_trunc_sat_f32_u, .f32 b => .ok (.i64 (Float32.ofBits b).toUInt64)
  | .i64_trunc_sat_f64_s, .f64 b => .ok (.i64 (Float.ofBits b).toInt64.toUInt64)
  | .i64_trunc_sat_f64_u, .f64 b => .ok (.i64 (Float.ofBits b).toUInt64)
  | .f32_convert_i32_s, .i32 x => .ok (.f32 x.toInt32.toFloat32.toBits)
  | .f32_convert_i32_u, .i32 x => .ok (.f32 x.toFloat32.toBits)
  | .f32_convert_i64_s, .i64 x => .ok (.f32 x.toInt64.toFloat32.toBits)
  | .f32_convert_i64_u, .i64 x => .ok (.f32 x.toFloat32.toBits)
  | .f64_convert_i32_s, .i32 x => .ok (.f64 x.toInt32.toFloat.toBits)
  | .f64_convert_i32_u, .i32 x => .ok (.f64 x.toFloat.toBits)
  | .f64_convert_i64_s, .i64 x => .ok (.f64 x.toInt64.toFloat.toBits)
  | .f64_convert_i64_u, .i64 x => .ok (.f64 x.toFloat.toBits)
  | .f32_demote_f64, .f64 b => .ok (.f32 (canon32 (Float.ofBits b).toFloat32))
  | .f64_promote_f32, .f32 b => .ok (.f64 (canon64 (Float32.ofBits b).toFloat))
  | .i32_reinterpret_f32, .f32 b => .ok (.i32 b)
  | .i64_reinterpret_f64, .f64 b => .ok (.i64 b)
  | .f32_reinterpret_i32, .i32 x => .ok (.f32 x)
  | .f64_reinterpret_i64, .i64 x => .ok (.f64 x)
  | _, _ => .error (.host "conversion applied to a value of the wrong type")

end Wasm.Numeric
