import Binary.Code.Part10
import NearLogic.Rules.CallWasm
import NearLogic.Tactic.Step

/-!
# `<U128 as From<u128>>::from` (function 566), in the metered logic

`from(out, lo, hi)` writes the `u128` `lo + 2^64 hi` to the 16 bytes at `out`,
little-endian, the high word first:

```wat
local.get 0  local.get 2  i64.store offset=8
local.get 0  local.get 1  i64.store offset=0
```

`f566_spec` is its `MFunSpec`: 6 instructions (the harness's `u128From`
counts 17 = the activation 11, paid by the caller, and these 6). The bytes
written are `u128Bytes lo hi`, whose little-endian value is
`lo + 2^64 * hi` (`decodeLE_u128Bytes`), the harness's postcondition.
-/

namespace WNear.Binary.U128From

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-! ## Bytes -/

/-- The 16 bytes `from(out, lo, hi)` writes: `lo`, then `hi`, little-endian. -/
def u128Bytes (lo hi : UInt64) : List UInt8 := storeBytes (.i64 lo) 8 ++ storeBytes (.i64 hi) 8

@[simp] theorem storeBytes_length (v : Value) (k : Nat) : (storeBytes v k).length = k := by
  simp [storeBytes]

@[simp] theorem u128Bytes_length (lo hi : UInt64) : (u128Bytes lo hi).length = 16 := by
  simp [u128Bytes]

theorem decodeLE_append (a b : List UInt8) :
    Memory.decodeLE (a ++ b) = Memory.decodeLE a + 256 ^ a.length * Memory.decodeLE b := by
  induction a with
  | nil => simp [Memory.decodeLE]
  | cons x xs ih =>
    simp only [Memory.decodeLE, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256]
    omega

theorem decodeLE_storeBytes_i64 (x : UInt64) : Memory.decodeLE (storeBytes (.i64 x) 8) = x.toNat := by
  have hx := x.toNat_lt
  simp [storeBytes, storeRaw, Memory.decodeLE, List.range, List.range.loop,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The value written is `lo + 2^64 * hi`. -/
theorem decodeLE_u128Bytes (lo hi : UInt64) :
    Memory.decodeLE (u128Bytes lo hi) = lo.toNat + 2 ^ 64 * hi.toNat := by
  rw [u128Bytes, decodeLE_append, decodeLE_storeBytes_i64, decodeLE_storeBytes_i64]
  simp

section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem memBytes_split (n i k : Nat) (ob : List UInt8) (h : k ≤ ob.length) :
    memBytes (H := NearState) (GF := GF) n i ob ⊢
      n ↦[wms][ i ] (ob.take k) ∗ n ↦[wms][ i + k ] (ob.drop k) := by
  have e := memBytes_append (GF := GF) (H := NearState) n i (ob.take k) (ob.drop k)
  rw [List.take_append_drop, List.length_take, show min k ob.length = k by omega] at e
  exact e.1

theorem memBytes_join (n i k : Nat) (a b : List UInt8) (h : a.length = k) :
    memBytes (H := NearState) (GF := GF) n i a ∗ n ↦[wms][ i + k ] b ⊢ n ↦[wms][ i ] (a ++ b) := by
  have e := memBytes_append (GF := GF) (H := NearState) n i a b
  rw [h] at e
  exact e.2

variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {Φ : Post NearState GF} {Cg R : Nat}

/-- The body of `U128::from`: 6 instructions, `u128Bytes lo hi` at `out`. -/
theorem body_spec (f : Frame) (out : UInt32) (lo hi : UInt64) (n : Nat) (ob : List UInt8)
    (hob : ob.length = 16)
    (h0 : f.locals[0]? = some (.i32 out)) (h1 : f.locals[1]? = some (.i64 lo))
    (h2 : f.locals[2]? = some (.i64 hi)) (hn : f.mi.memAddrs[0]? = some n) :
    credits Cg (6 * cfg.regularOpCost + R) ∗ n ↦[wms][ out.toNat ] ob ∗
      (credits Cg R -∗ n ↦[wms][ out.toNat ] u128Bytes lo hi -∗ Φ.normal [] f)
      ⊢ mwpi cfg lim d f [] f566.body Φ := by
  iintro ⟨Hc, Ho, HΦ⟩
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨Ho1, Ho2⟩
  simp only [f566]
  mstep; mstep; mstep [Ho2]   -- out+8 := hi
  mstep; mstep; mstep [Ho1]   -- out   := lo
  iapply HΦ $$ Hc
  rw [u128Bytes]
  iapply memBytes_join n out.toNat 8 _ _ (by simp) $$ [Ho1 Ho2]
  isplitl [Ho1] <;> iassumption

end Body

/-! ## The function -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition of `from(out, lo, hi)`: the arguments and the 16 bytes at `out`. -/
def pre (n : Nat) (out : UInt32) (lo hi : UInt64) (ob : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i64 lo, .i64 hi]⌝ ∗ n ↦[wms][ out.toNat ] ob)

/-- The postcondition: no results, `lo + 2^64 hi` at `out` (`decodeLE_u128Bytes`). -/
def post (n : Nat) (out : UInt32) (lo hi : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[wms][ out.toNat ] u128Bytes lo hi)

/-- `<U128 as From<u128>>::from` (function 566 of `contract.wasm`), at any
call depth, for the memory `n` of its instance: 6 instructions. -/
theorem f566_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out : UInt32) (lo hi : UInt64)
    (ob : List UInt8) (hob : ob.length = 16) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f566 Cg (pre n out lo hi ob)
      (fun _ => 6 * cfg.regularOpCost) (post n out lo hi) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  iapply body_spec ⟨entryLocals f566 [.i32 out, .i64 lo, .i64 hi], inst, mi⟩ out lo hi n ob hob
    rfl rfl rfl hn
  isplitl [Hc]; iexact Hc
  isplitl [Ho]; iexact Ho
  iintro Hc Ho
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold post
  iframe Hc Ho
  ipureintro; rfl

end Spec

end WNear.Binary.U128From
