import NearFastVM.Ins

/-!
# Helpers of the interpreter loop

The result of a run, the gas bookkeeping and the host call. The loop keeps the gas it has spent since the last
synchronisation in a register (`acc`) and the room left before either limit is hit in another (`lim`): a charge is
an addition and a comparison. When a charge does not fit, `gasFail` replays it on the host state with
`Wasm.Near.chargeHost`, which is exactly what `runMetered` does for every charge, so the error and the burnt gas
left behind are the specification's.
-/

namespace NearFastVM

open Wasm Wasm.Near

inductive Exit where
  | done (values : List Value)
  | trap (t : Trap)
  | gasFail (e : HostError)
  /-- The engine cannot run this (a function it does not compile, a host that dropped the memory): the run is
  discarded and the specification runs from the start. -/
  | unsupported

structure Final where
  exit : Exit
  host : NearState
  pg : Array ByteArray
  gl : Array UInt32

instance : Inhabited Final :=
  ⟨{ exit := .unsupported, host := default, pg := #[], gl := default }⟩

/-- Spend `acc` burnt gas on the host state, as `acc` successful `chargeHost` calls would. -/
def syncGas (host : NearState) (acc : UInt64) : NearState :=
  if acc == 0 then host
  else
    { host with
      gas := { host.gas with burnt := host.gas.burnt + acc.toNat },
      gasProfile := { host.gasProfile with wasm := host.gasProfile.wasm + acc.toNat } }

/-- How much more may be burnt before `GasCounter.deduct` fails, given that the counter is within its limits
(otherwise nothing fits and every charge takes the exact path). -/
def limOf (host : NearState) : UInt64 :=
  let g := host.gas
  if g.burnt ≤ g.maxBurnt ∧ g.burnt + g.promises ≤ g.prepaid then
    let room := min (g.maxBurnt - g.burnt) (g.prepaid - (g.burnt + g.promises))
    if room < 2 ^ 62 then room.toUInt64 else (2 ^ 62).toUInt64
  else 0

/-- A charge of `cost` that does not fit after `acc0` burnt since the last synchronisation. -/
def gasFail (host : NearState) (acc0 : UInt64) (cost : Nat) (pg : Array ByteArray)
    (gl : Array UInt32) : Final :=
  let host := syncGas host acc0
  let r := chargeHost host cost
  match r.2 with
  | some e => { exit := .gasFail e, host := r.1, pg, gl }
  | none => { exit := .unsupported, host, pg, gl }

def finish (host : NearState) (acc : UInt64) (pg : Array ByteArray) (gl : Array UInt32)
    (exit : Exit) : Final :=
  { exit, host := syncGas host acc, pg, gl }

/-! ## Slots

A value slot is two consecutive 32-bit words of an `Array UInt32` (low word first): `Float.ofBits` and
`Float.toBits` canonicalise NaNs, so a `FloatArray` cannot hold the bit pattern of an `i64`, and an
`Array UInt64` allocates for every store. A word of an `Array UInt32` is a boxed scalar. A slot holding an
`i32` or `f32` is read and written through its low word only; the high word is whatever it was. Slot numbers
are word indices. -/

@[inline]
def rd32 (st : Array UInt32) (i : USize) : UInt32 :=
  st[i.toNat]!

@[inline]
def rd (st : Array UInt32) (i : USize) : UInt64 :=
  (st[i.toNat]!).toUInt64 ||| ((st[i.toNat + 1]!).toUInt64 <<< 32)

@[inline]
def wr32 (st : Array UInt32) (i : USize) (v : UInt32) : Array UInt32 :=
  st.set! i.toNat v

@[inline]
def wr (st : Array UInt32) (i : USize) (v : UInt64) : Array UInt32 :=
  (st.set! i.toNat v.toUInt32).set! (i.toNat + 1) (v >>> 32).toUInt32

/-- Move `n` slots from `src` to `dst` (`dst ≤ src`). -/
def moveSlots (st : Array UInt32) (src dst : USize) (n : Nat) : Array UInt32 :=
  Id.run do
    let mut st := st
    for k in [0:2 * n] do
      st := st.set! (dst + k.toUSize).toNat st[(src + k.toUSize).toNat]!
    return st

/-- Zero `n` slots from `from_`. -/
def zeroSlots (st : Array UInt32) (from_ : USize) (n : Nat) : Array UInt32 :=
  Id.run do
    let mut st := st
    for k in [0:2 * n] do
      st := st.set! (from_ + k.toUSize).toNat 0
    return st

def growStack (st : Array UInt32) (need : Nat) : Array UInt32 :=
  st ++ Array.replicate (max need (2 * st.size) - st.size) 0

def valOfBits : ValType → UInt64 → Value
  | .num .i32, b => .i32 b.toUInt32
  | .num .i64, b => .i64 b
  | .num .f32, b => .f32 b.toUInt32
  | .num .f64, b => .f64 b
  | .ref t, _ => .ref (.null t)

def bitsOfVal : Value → UInt64
  | .i32 v => v.toUInt64
  | .f32 v => v.toUInt64
  | .i64 v => v
  | .f64 v => v
  | .ref _ => 0

def argsFrom (st : Array UInt32) : List ValType → USize → List Value
  | [], _ => []
  | t :: ts, i => valOfBits t (rd st i) :: argsFrom st ts (i + 2)

def putResults (st : Array UInt32) : List Value → USize → Array UInt32
  | [], _ => st
  | v :: vs, i => putResults (wr st i (bitsOfVal v)) vs (i + 2)

def resultsOf (st : Array UInt32) : List ValType → USize → List Value :=
  argsFrom st

/-! ## Host calls -/

structure HostRes where
  st : Array UInt32
  pg : Array ByteArray
  host : NearState
  lim : UInt64
  trap : Option Trap
  /-- The host gave no memory back although it was given one. -/
  dropped : Bool

/-- Call a host function with the arguments at `base`: the gas spent so far is settled first, the memory goes
in and comes back, and the results are written from `base`. -/
def callHost (cx : Ctx) (fn : HostFn NearState) (base : USize) (st : Array UInt32)
    (pg : Array ByteArray) (host : NearState) (acc : UInt64) : HostRes :=
  let args := argsFrom st fn.type.params base
  let host := syncGas host acc
  if cx.hasMem then
    match fn.call host (some { pages := pg, max := cx.memMax }) args with
    | .«return» values host' (some m) =>
      { st := putResults st values base, pg := m.pages, host := host', lim := limOf host',
        trap := none, dropped := false }
    | .trap reason host' (some m) =>
      { st, pg := m.pages, host := host', lim := 0, trap := some reason, dropped := false }
    | .«return» _ host' none | .trap _ host' none =>
      { st, pg := #[], host := host', lim := 0, trap := none, dropped := true }
  else
    match fn.call host none args with
    | .«return» values host' _ =>
      { st := putResults st values base, pg, host := host', lim := limOf host', trap := none,
        dropped := false }
    | .trap reason host' _ =>
      { st, pg, host := host', lim := 0, trap := some reason, dropped := false }

/-! ## Integer operations -/

@[inline]
def clz32 (a : UInt32) : UInt32 :=
  if a == 0 then 32 else 31 - a.log2

@[inline]
def ctz32 (a : UInt32) : UInt32 :=
  if a == 0 then 32 else (a &&& (0 - a)).log2

@[inline]
def clz64 (a : UInt64) : UInt64 :=
  if a == 0 then 64 else 63 - a.log2

@[inline]
def ctz64 (a : UInt64) : UInt64 :=
  if a == 0 then 64 else (a &&& (0 - a)).log2

def popcnt32 (a : UInt32) : UInt32 :=
  let m1 : UInt32 := 0x55555555
  let m2 : UInt32 := 0x33333333
  let m4 : UInt32 := 0x0F0F0F0F
  let h : UInt32 := 0x01010101
  let a : UInt32 := a - ((a >>> 1) &&& m1)
  let a : UInt32 := (a &&& m2) + ((a >>> 2) &&& m2)
  let a : UInt32 := (a + (a >>> 4)) &&& m4
  (a * h) >>> 24

def popcnt64 (a : UInt64) : UInt64 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0F0F0F0F0F0F0F0F
  let h : UInt64 := 0x0101010101010101
  let a : UInt64 := a - ((a >>> 1) &&& m1)
  let a : UInt64 := (a &&& m2) + ((a >>> 2) &&& m2)
  let a : UInt64 := (a + (a >>> 4)) &&& m4
  (a * h) >>> 56

@[inline]
def rotl32 (a b : UInt32) : UInt32 :=
  let k := b % 32;
  (a <<< k) ||| (a >>> ((32 - k) % 32))

@[inline]
def rotr32 (a b : UInt32) : UInt32 :=
  let k := b % 32;
  (a >>> k) ||| (a <<< ((32 - k) % 32))

@[inline]
def rotl64 (a b : UInt64) : UInt64 :=
  let k := b % 64;
  (a <<< k) ||| (a >>> ((64 - k) % 64))

@[inline]
def rotr64 (a b : UInt64) : UInt64 :=
  let k := b % 64;
  (a >>> k) ||| (a <<< ((64 - k) % 64))

@[inline]
def shrs32 (a b : UInt32) : UInt32 :=
  (a.toInt32 >>> (b % 32).toInt32).toUInt32

@[inline]
def shrs64 (a b : UInt64) : UInt64 :=
  (a.toInt64 >>> (b % 64).toInt64).toUInt64

@[inline]
def divs32 (a b : UInt32) : UInt32 :=
  (a.toInt32 / b.toInt32).toUInt32

@[inline]
def rems32 (a b : UInt32) : UInt32 :=
  (a.toInt32 % b.toInt32).toUInt32

@[inline]
def divs64 (a b : UInt64) : UInt64 :=
  (a.toInt64 / b.toInt64).toUInt64

@[inline]
def rems64 (a b : UInt64) : UInt64 :=
  (a.toInt64 % b.toInt64).toUInt64

@[inline]
def b2u (b : Bool) : UInt64 :=
  if b then 1 else 0

@[inline]
def b2u32 (b : Bool) : UInt32 :=
  if b then 1 else 0

/-! ## Cold operations: floating point, truncations and conversions, through `Wasm.Numeric` -/

def cvtIn : CvtOp → UInt64 → Value
  | .f32_convert_i32_s, b | .f32_convert_i32_u, b | .f64_convert_i32_s, b | .f64_convert_i32_u, b |
    .i64_extend_i32_s, b | .i64_extend_i32_u, b | .f32_reinterpret_i32, b => .i32 b.toUInt32
  | .f32_convert_i64_s, b | .f32_convert_i64_u, b | .f64_convert_i64_s, b | .f64_convert_i64_u, b |
    .f64_reinterpret_i64, b | .i32_wrap_i64, b => .i64 b
  | .i32_trunc_f32_s, b | .i32_trunc_f32_u, b | .i64_trunc_f32_s, b | .i64_trunc_f32_u, b |
    .f64_promote_f32, b | .i32_reinterpret_f32, b | .i32_trunc_sat_f32_s, b | .i32_trunc_sat_f32_u,
    b | .i64_trunc_sat_f32_s, b | .i64_trunc_sat_f32_u, b => .f32 b.toUInt32
  | .i32_trunc_f64_s, b | .i32_trunc_f64_u, b | .i64_trunc_f64_s, b | .i64_trunc_f64_u, b |
    .f32_demote_f64, b | .i64_reinterpret_f64, b | .i32_trunc_sat_f64_s, b | .i32_trunc_sat_f64_u,
    b | .i64_trunc_sat_f64_s, b | .i64_trunc_sat_f64_u, b => .f64 b

/-- Execute a floating-point or conversion instruction on the operands at `i`; the result goes to `i`. -/
def execCold (ins : Instr) (st : Array UInt32) (i : USize) : Except Trap UInt64 :=
  let a := rd st i
  let b := rd st (i + 2)
  match ins with
  | .f32_unop op => .ok (Numeric.funop32 op a.toUInt32).toUInt64
  | .f64_unop op => .ok (Numeric.funop64 op a)
  | .f32_binop op => .ok (Numeric.fbinop32 op a.toUInt32 b.toUInt32).toUInt64
  | .f64_binop op => .ok (Numeric.fbinop64 op a b)
  | .f32_relop op => .ok (b2u (Numeric.frelop32 op a.toUInt32 b.toUInt32))
  | .f64_relop op => .ok (b2u (Numeric.frelop64 op a b))
  | .cvt op =>
    match Numeric.cvt op (cvtIn op a) with
    | .ok v => .ok (bitsOfVal v)
    | .error t => .error t
  | _ => .error (.host "cold: not a floating-point instruction")

end NearFastVM
