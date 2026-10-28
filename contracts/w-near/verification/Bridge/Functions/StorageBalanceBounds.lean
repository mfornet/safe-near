import Bridge.Functions.FtTotalSupplyGetter
import Bridge.Functions.FmtMulti3
import Bridge.Functions.BorshFT
import Bridge.Functions.ReadRegister
import Bridge.Functions.Getter
import Binary.Code.Part05

/-!
# `storage_balance_bounds` (418), `env::storage_byte_cost` (553) and the getter 230, in the metered logic

```wat
;; 553 storage_byte_cost(out): the u128 10^19 (near-sdk 3.1.0 hardcodes the byte price)
local.get 0  i64.const 0  i64.store offset=8
local.get 0  i64.const 10^19  i64.store

;; 418 storage_balance_bounds(out, contract): an 80-byte frame at sp' = sp - 80
x := [contract + 16]                                   ;; account_storage_usage, a u64
storage_byte_cost(sp' + 64)                            ;; (lo_c, hi_c) = (10^19, 0)
__multi3(sp' + 32, hi_c, 0, x, 0)                      ;; hi_c * x
__multi3(sp' + 48, x, 0, lo_c, 0)                      ;; x * lo_c
block
  br_if 0 ([sp' + 40] ≠ 0 || [sp' + 56] + [sp' + 32] overflows)   ;; checked_mul's overflow
  from(sp' + 16, lo, hi); from(sp', lo, hi)            ;; 566, twice: min and max
  out := StorageBalanceBounds { min, max: Some(max) }  ;; min, the tag 1, max
  return
end
panic("attempt to multiply with overflow")             ;; 853, not reached

;; 230 storage_minimum_balance(out, contract): a 48-byte frame at sp'' = sp - 48
storage_balance_bounds(sp'' + 8, contract)             ;; 418
out := [sp'' + 8 .. sp'' + 24]                         ;; the bounds' min
```

The overflow branch is unreachable: `hi_c = 0`, so the first product is 0, and the second is
`x * 10^19 < 2^64 · 10^19 < 2^128`. The bounds are `boundsBytes N`, `N = x * 10^19`: the `u128`
`N` (`u128Of N`), the `Option` tag 1 as a `u64`, and `N` again.

* `f553_spec`: 4 instructions.
* `f418_spec`: 109 instructions, the calls' activations and their callees (553: 4, 954: 60
  twice, 566: 6 twice); `cost418`.
* `f230_spec`: 418's, and 230's own 26 instructions; `cost230`.
-/

namespace WNear.Binary.StorageBalanceBounds

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.U128From (u128Bytes memBytes_split memBytes_join decodeLE_storeBytes_i64)

/-! ## Bytes -/

/-- The 16 bytes of the `u128` `N mod 2^128`, little-endian. -/
def u128Of (N : Nat) : List UInt8 := u128Bytes (UInt64.ofNat N) (UInt64.ofNat (N / 2 ^ 64))

/-- The 40 bytes of `StorageBalanceBounds { min: N, max: Some(N) }`: `N`, the tag 1, `N`. -/
def boundsBytes (N : Nat) : List UInt8 := u128Of N ++ storeBytes (.i64 1) 8 ++ u128Of N

@[simp] theorem u128Of_length (N : Nat) : (u128Of N).length = 16 := by simp [u128Of]

@[simp] theorem boundsBytes_length (N : Nat) : (boundsBytes N).length = 40 := by
  simp [boundsBytes]

theorem u128Bytes_eq_u128Of (lo hi : UInt64) (N : Nat) (h : lo.toNat + 2 ^ 64 * hi.toNat = N) :
    u128Bytes lo hi = u128Of N := by
  have hl := lo.toNat_lt
  have hh := hi.toNat_lt
  have e1 : UInt64.ofNat N = lo := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_ofNat']; omega
  have e2 : UInt64.ofNat (N / 2 ^ 64) = hi := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_ofNat']; omega
  rw [u128Of, e1, e2]

/-- The value of `u128Of N` is `N mod 2^128`. -/
theorem decodeLE_u128Of (N : Nat) : Memory.decodeLE (u128Of N) = N % 2 ^ 128 := by
  rw [u128Of, U128From.decodeLE_u128Bytes]
  simp only [UInt64.toNat_ofNat']
  have := Nat.mod_mul (x := N) (a := 2 ^ 64) (b := 2 ^ 64)
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, this]

/-- An `i64` loaded from the bytes an `i64` store wrote is the stored value. -/
theorem load_storeBytes_i64 (x : UInt64) : UInt64.ofNat (Memory.decodeLE (storeBytes (.i64 x) 8)) = x := by
  rw [decodeLE_storeBytes_i64]; simp

/-! ## `env::storage_byte_cost` (553) -/

section F553

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition of `storage_byte_cost(out)`: the 16 bytes at `out`. -/
def pre553 (n : Nat) (out : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out]⌝ ∗ n ↦[wms][ out.toNat ] ob)

/-- The postcondition: `10^19` at `out`. -/
def post553 (n : Nat) (out : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[wms][ out.toNat ] u128Bytes 10000000000000000000 0)

/-- `env::storage_byte_cost` (function 553 of `contract.wasm`): 6 instructions, no host call. -/
theorem f553_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out : UInt32) (ob : List UInt8) (hob : ob.length = 16) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f553 Cg (pre553 n out ob)
      (fun _ => 6 * cfg.regularOpCost) (post553 n out) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre553 at HP
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨Ho1, Ho2⟩
  simp only [f553]
  mstep; mstep; mstep [Ho2]
  mstep; mstep; mstep [Ho1]
  iunfold post553
  iframe Hc
  isplitr
  · ipureintro; rfl
  rw [u128Bytes]
  iapply memBytes_join n out.toNat 8 _ _ (by simp) $$ [Ho1 Ho2]
  isplitl [Ho1] <;> iassumption

end F553

/-! ## `storage_balance_bounds` (418) -/

/-- The `u64` an `i64.load` reads from the 8 bytes `xb`. -/
def xOf (xb : List UInt8) : UInt64 := UInt64.ofNat (Memory.decodeLE xb)

/-- `x * 10^19` fits a `u128` for every `u64` `x`: `checked_mul` does not overflow. -/
theorem mul_price_lt (x : UInt64) : x.toNat * 10000000000000000000 < 2 ^ 128 := by
  have := x.toNat_lt
  have : x.toNat * 10000000000000000000 ≤ (2 ^ 64 - 1) * 10000000000000000000 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem tsub' (x y : UInt32) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le x y (UInt32.le_iff_toNat_le.mpr h)

section F418

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk)
open WNear.Binary.BorshFT (splitB joinB stkJ stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.AllocNewCell (memBytes_addr)

/-- The precondition of `storage_balance_bounds(out, contract)`: the stack pointer `sp` in
global `g`, the 80 bytes of the frame below it, the 40 bytes at `out` and the
`account_storage_usage` bytes `xb` at `contract + 16`. -/
def pre418 (n g : Nat) (gt : GlobalType) (sp out ft : UInt32) (ob xb : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 ft]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 80) 80 ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ft.toNat + 16 ] xb)

/-- The postcondition: the bounds `{ min: x·10^19, max: Some(x·10^19) }` at `out`. -/
def post418 (n g : Nat) (gt : GlobalType) (sp out ft : UInt32) (xb : List UInt8)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 80) 80 ∗
    n ↦[wms][ out.toNat ] boundsBytes ((xOf xb).toNat * 10000000000000000000) ∗
    n ↦[wms][ ft.toNat + 16 ] xb)

/-- The cost of `storage_balance_bounds`, activation excluded. -/
def cost418 (cfg : WasmConfig) : Nat := 314 * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `storage_balance_bounds` (function 418 of `contract.wasm`), for the memory `n` and the
shadow-stack global `g` of its instance: the bounds of the `u64` storage usage at
`contract + 16` times `10^19`, the overflow panic not reached. -/
theorem f418_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g a553 a954 a566 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (h553 : mi.funcAddrs[553]? = some a553) (h954 : mi.funcAddrs[954]? = some a954)
    (h566 : mi.funcAddrs[566]? = some a566) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ft : UInt32) (hsp : 80 ≤ sp.toNat) (hout : out.toNat + 40 ≤ 2 ^ 32)
    (ob xb : List UInt8) (hob : ob.length = 40) (hxb : xb.length = 8) :
    a553 ↪[wf] FuncInst.wasm types[0]! inst f553 ∗ a954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗
      a566 ↪[wf] FuncInst.wasm types[4]! inst f566 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f418 Cg (pre418 n g gt sp out ft ob xb)
        (fun _ => cost418 cfg) (post418 n g gt sp out ft xb) := by
  iintro ⟨#F553, #F954, #F566, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre418 at HP
  icases HP with ⟨%hargs, Hg, Hfr, Ho, Hx⟩
  subst hargs
  unfold cost418
  have hlt := sp.toNat_lt
  have e0 : (sp - 80).toNat = sp.toNat - 80 := by rw [tsub' _ _ (by simp; omega)]; simp
  have a64 : (sp - 80 + 64).toNat = sp.toNat - 16 := by simp [UInt32.toNat_add, e0]; omega
  have a48 : (sp - 80 + 48).toNat = sp.toNat - 32 := by simp [UInt32.toNat_add, e0]; omega
  have a32 : (sp - 80 + 32).toNat = sp.toNat - 48 := by simp [UInt32.toNat_add, e0]; omega
  have a16 : (sp - 80 + 16).toNat = sp.toNat - 64 := by simp [UInt32.toNat_add, e0]; omega
  icases stkSp 16 64 rfl $$ Hfr with ⟨F0, Hfr⟩
  icases stkSp 16 48 rfl $$ Hfr with ⟨F16, Hfr⟩
  icases stkSp 16 32 rfl $$ Hfr with ⟨F32, Hfr⟩
  icases stkSp 16 16 rfl $$ Hfr with ⟨F48, F64⟩
  icases stk_bytes' $$ F0 with ⟨%b0, %hb0, F0⟩
  icases stk_bytes' $$ F16 with ⟨%b16, %hb16, F16⟩
  icases stk_bytes' $$ F32 with ⟨%b32, %hb32, F32⟩
  icases stk_bytes' $$ F48 with ⟨%b48, %hb48, F48⟩
  icases stk_bytes' $$ F64 with ⟨%b64, %hb64, F64⟩
  have t0 : types[0]!.params.length = 1 := rfl
  have t8 : types[8]!.params.length = 5 := rfl
  have t4 : types[4]!.params.length = 3 := rfl
  simp only [f418]
  -- sp' := sp - 80; x := [contract + 16]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep [Hx]; mstep
  -- storage_byte_cost(sp' + 64)
  mstep; mstep; mstep
  mcall (f553_spec cfg lim (d + 1) types[0]! rfl inst mi n hn Cg (sp - 80 + 64) b64 hb64) using [F64]
  · iunfold pre553
    ihave F64 := memBytes_addr (b := (sp - 80 + 64).toNat) (by omega) $$ F64
    iframe F64
    ipureintro; rfl
  iunfold post553 at HQ
  icases HQ with ⟨%hrs, F64⟩
  subst hrs
  ihave F64 := memBytes_addr (b := sp.toNat - 16) (by omega) $$ F64
  rw [u128Bytes]
  icases splitB (a := sp.toNat - 16) (b := sp.toNat - 8) _ _ (by simp; omega) $$ F64 with ⟨F64, F72⟩
  -- __multi3(sp' + 32, hi_c, 0, x, 0)
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [F72]
  mstep; mstep; mstep
  rw [load_storeBytes_i64]
  mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! rfl inst mi n hn Cg (sp - 80 + 32) 0 0
      (UInt64.ofNat (Memory.decodeLE xb)) 0 b32 hb32) using [F32]
  · iunfold FmtMulti3.pre
    ihave F32 := memBytes_addr (b := (sp - 80 + 32).toNat) (by omega) $$ F32
    iframe F32
    ipureintro; rfl
  iunfold FmtMulti3.post at HQ
  icases HQ with ⟨%hrs, %lo1, %hi1, %h1, F32⟩
  subst hrs
  have h1' : lo1.toNat + 2 ^ 64 * hi1.toNat = 0 := by rw [h1]; simp
  have hlo1 : lo1 = 0 := UInt64.toNat_inj.mp (by simp; omega)
  have hhi1 : hi1 = 0 := UInt64.toNat_inj.mp (by simp; omega)
  subst hlo1 hhi1
  -- __multi3(sp' + 48, x, 0, lo_c, 0)
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [F64]; mstep
  rw [load_storeBytes_i64]
  mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! rfl inst mi n hn Cg (sp - 80 + 48)
      (UInt64.ofNat (Memory.decodeLE xb)) 0 10000000000000000000 0 b48 hb48) using [F48]
  · iunfold FmtMulti3.pre
    ihave F48 := memBytes_addr (b := (sp - 80 + 48).toNat) (by omega) $$ F48
    iframe F48
    ipureintro; rfl
  iunfold FmtMulti3.post at HQ
  icases HQ with ⟨%hrs, %lo2, %hi2, %h2, F48⟩
  subst hrs
  ihave F32 := memBytes_addr (b := sp.toNat - 48) (by omega) $$ F32
  ihave F48 := memBytes_addr (b := sp.toNat - 32) (by omega) $$ F48
  simp only [u128Bytes]
  icases splitB (a := sp.toNat - 48) (b := sp.toNat - 40) _ _ (by simp; omega) $$ F32 with ⟨F32, F40⟩
  icases splitB (a := sp.toNat - 32) (b := sp.toNat - 24) _ _ (by simp; omega) $$ F48 with ⟨F48, F56⟩
  -- the overflow check: not taken
  mstep
  mstep; mstep [F40]; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep [F56]; mstep
  mstep; mstep [F32]; mstep; mstep; mstep; mstep; mstep
  simp only [load_storeBytes_i64, UInt64.add_zero]
  mstep_not_taken with (simp [Numeric.bool, Numeric.irelop64])
  -- from(sp' + 16, lo, hi)
  mstep; mstep; mstep; mstep; mstep [F48]; mstep; mstep
  simp only [load_storeBytes_i64]
  mcall (U128From.f566_spec cfg lim (d + 1) types[4]! rfl inst mi n hn Cg (sp - 80 + 16) lo2 hi2 b16 hb16)
    using [F16]
  · iunfold U128From.pre
    ihave F16 := memBytes_addr (b := (sp - 80 + 16).toNat) (by omega) $$ F16
    iframe F16
    ipureintro; rfl
  iunfold U128From.post at HQ
  icases HQ with ⟨%hrs, F16⟩
  subst hrs
  ihave F16 := memBytes_addr (b := sp.toNat - 64) (by omega) $$ F16
  simp only [u128Bytes]
  icases splitB (a := sp.toNat - 64) (b := sp.toNat - 56) _ _ (by simp; omega) $$ F16 with ⟨F16, F24⟩
  mstep; mstep; mstep; mstep; mstep; mstep [F24]; mstep
  mstep; mstep [F16]; mstep
  -- from(sp', lo, hi)
  mstep; mstep; mstep
  simp only [load_storeBytes_i64]
  mcall (U128From.f566_spec cfg lim (d + 1) types[4]! rfl inst mi n hn Cg (sp - 80) lo2 hi2 b0 hb0)
    using [F0]
  · iunfold U128From.pre
    ihave F0 := memBytes_addr (b := (sp - 80).toNat) (by omega) $$ F0
    iframe F0
    ipureintro; rfl
  iunfold U128From.post at HQ
  icases HQ with ⟨%hrs, F0⟩
  subst hrs
  ihave F0 := memBytes_addr (b := sp.toNat - 80) (by omega) $$ F0
  simp only [u128Bytes]
  icases splitB (a := sp.toNat - 80) (b := sp.toNat - 72) _ _ (by simp; omega) $$ F0 with ⟨F0, F8⟩
  -- out := { min, Some(max) }
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases memBytes_split n (out.toNat + 8) 8 _ (by simp; omega) $$ Ho with ⟨O8, Ho⟩
  icases memBytes_split n (out.toNat + 8 + 8) 8 _ (by simp; omega) $$ Ho with ⟨O16, Ho⟩
  icases memBytes_split n (out.toNat + 8 + 8 + 8) 8 _ (by simp; omega) $$ Ho with ⟨O24, O32⟩
  mstep; mstep [F0]; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [F8]; mstep [O32]
  mstep; mstep; mstep; mstep; mstep [O24]
  mstep; mstep; mstep [O8]
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep [O16]
  -- sp += 80
  mstep; mstep; mstep; mstep [Hg]
  simp only [load_storeBytes_i64]
  rw [show sp - 80 + 80 = sp by simp]
  mstep
  -- the bounds: N = x * 10^19, no overflow
  have hN : lo2.toNat + 2 ^ 64 * hi2.toNat = (xOf xb).toNat * 10000000000000000000 := by
    rw [h2, xOf]; simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt (mul_price_lt _)
  have hu := u128Bytes_eq_u128Of lo2 hi2 _ hN
  ihave J := joinB (a := out.toNat + 8 + 8 + 8) (b := out.toNat + 8 + 8 + 8 + 8) (storeBytes (.i64 lo2) 8) _ (by simp) $$ [O24 O32]
  · iframe O24 O32
  ihave J := joinB (a := out.toNat + 8 + 8) (b := out.toNat + 8 + 8 + 8) (storeBytes (.i64 1) 8) _ (by simp) $$ [O16 J]
  · iframe O16 J
  ihave J := joinB (a := out.toNat + 8) (b := out.toNat + 8 + 8) (storeBytes (.i64 hi2) 8) _ (by simp) $$ [O8 J]
  · iframe O8 J
  ihave J := joinB (a := out.toNat) (b := out.toNat + 8) (storeBytes (.i64 lo2) 8) _ (by simp) $$ [O0 J]
  · iframe O0 J
  ihave J := AllocNewCell.memBytes_eq (bs' := boundsBytes ((xOf xb).toNat * 10000000000000000000))
    (by rw [boundsBytes, ← hu, u128Bytes]; simp) $$ J
  ihave K := joinB (a := sp.toNat - 16) (b := sp.toNat - 8) (storeBytes (.i64 10000000000000000000) 8) _ (by simp; omega) $$ [F64 F72]
  · iframe F64 F72
  ihave K := joinB (a := sp.toNat - 24) (b := sp.toNat - 16) (storeBytes (.i64 hi2) 8) _ (by simp; omega) $$ [F56 K]
  · iframe F56 K
  ihave K := joinB (a := sp.toNat - 32) (b := sp.toNat - 24) (storeBytes (.i64 lo2) 8) _ (by simp; omega) $$ [F48 K]
  · iframe F48 K
  ihave K := joinB (a := sp.toNat - 40) (b := sp.toNat - 32) (storeBytes (.i64 0) 8) _ (by simp; omega) $$ [F40 K]
  · iframe F40 K
  ihave K := joinB (a := sp.toNat - 48) (b := sp.toNat - 40) (storeBytes (.i64 0) 8) _ (by simp; omega) $$ [F32 K]
  · iframe F32 K
  ihave K := joinB (a := sp.toNat - 56) (b := sp.toNat - 48) (storeBytes (.i64 hi2) 8) _ (by simp; omega) $$ [F24 K]
  · iframe F24 K
  ihave K := joinB (a := sp.toNat - 64) (b := sp.toNat - 56) (storeBytes (.i64 lo2) 8) _ (by simp; omega) $$ [F16 K]
  · iframe F16 K
  ihave K := joinB (a := sp.toNat - 72) (b := sp.toNat - 64) (storeBytes (.i64 hi2) 8) _ (by simp; omega) $$ [F8 K]
  · iframe F8 K
  ihave K := joinB (a := sp.toNat - 80) (b := sp.toNat - 72) (storeBytes (.i64 lo2) 8) _ (by simp; omega) $$ [F0 K]
  · iframe F0 K
  ihave K := stkB (b := sp.toNat - 80) (k := 80) _ rfl (by simp) $$ K
  iframe Hc
  iunfold post418
  iframe Hg K J Hx
  ipureintro; rfl

end F418

/-! ## The getter 230 -/

/-- The minimum balance a getter reads from the contract's bytes `cb`: the `u64` at offset 16,
times `10^19`. -/
def minOf (cb : List UInt8) : Nat := (xOf ((cb.drop 16).take 8)).toNat * 10000000000000000000

/-- The cost of 230, activation excluded: its 27 instructions, 418's activation (14) and
`cost418`. -/
def cost230 (cfg : WasmConfig) : Nat := 355 * cfg.regularOpCost

section F230

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk)
open WNear.Binary.BorshFT (splitB joinB stkJ stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.Getter (getterPre getterPost)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The getter 230 of `storage_minimum_balance` (`storage_balance_bounds().min`), in the shape
`Getter.getterPre`/`getterPost` with a frame of 128 bytes (its 48 and 418's 80): `u128Of
(minOf cb)` at `out`. -/
theorem f230_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g a418 a553 a954 a566 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (h418 : mi.funcAddrs[418]? = some a418) (h553 : mi.funcAddrs[553]? = some a553)
    (h954 : mi.funcAddrs[954]? = some a954) (h566 : mi.funcAddrs[566]? = some a566)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ft : UInt32) (hsp : 128 ≤ sp.toNat) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hft : ft.toNat + 40 ≤ 2 ^ 32) (ob cb : List UInt8) (hob : ob.length = 16) (hcb : cb.length = 40) :
    a418 ↪[wf] FuncInst.wasm types[14]! inst f418 ∗ a553 ↪[wf] FuncInst.wasm types[0]! inst f553 ∗
      a954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗ a566 ↪[wf] FuncInst.wasm types[4]! inst f566 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f230 Cg (getterPre n g gt sp out ft 128 ob cb)
        (fun _ => cost230 cfg) (getterPost n g gt sp out ft 128 (u128Of (minOf cb)) cb) := by
  iintro ⟨#F418, #F553, #F954, #F566, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold getterPre at HP
  icases HP with ⟨%hargs, Hg, Hfr, Ho, Hcb⟩
  subst hargs
  unfold cost230
  have hlt := sp.toNat_lt
  have e0 : (sp - 48).toNat = sp.toNat - 48 := by rw [tsub' _ _ (by simp; omega)]; simp
  have a8 : (sp - 48 + 8).toNat = sp.toNat - 40 := by simp [UInt32.toNat_add, e0]; omega
  icases stkSp 80 48 rfl $$ Hfr with ⟨F418, Hfr⟩
  icases stkSp 8 40 rfl $$ Hfr with ⟨F0, F8⟩
  icases stk_bytes' $$ F8 with ⟨%b8, %hb8, F8⟩
  icases memBytes_split n ft.toNat 16 cb (by omega) $$ Hcb with ⟨C0, C16⟩
  icases memBytes_split n (ft.toNat + 16) 8 _ (by simp; omega) $$ C16 with ⟨C16, C24⟩
  have t14 : types[14]!.params.length = 2 := rfl
  simp only [f230]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  have hc418 : cost418 cfg = 314 * cfg.regularOpCost := rfl
  mstep; mstep; mstep; mstep
  mcall (f418_spec cfg lim (d + 1) types[14]! rfl inst mi n g a553 a954 a566 hn hg h553 h954 h566
      (by omega) Cg gt (sp - 48) (sp - 48 + 8) ft (by omega) (by omega) b8
      ((cb.drop 16).take 8) hb8 (by simp; omega)) using [Hg F418 F8 C16]
  · iunfold pre418
    ihave F418 := stkA (b := (sp - 48).toNat - 80) (by omega) $$ F418
    ihave F8 := memBytes_addr (b := (sp - 48 + 8).toNat) (by omega) $$ F8
    iframe Hg F418 F8 C16
    ipureintro; rfl
  iunfold post418 at HQ
  icases HQ with ⟨%hrs, Hg, F418, F8, C16⟩
  subst hrs
  ihave F8 := memBytes_addr (b := sp.toNat - 40) (by omega) $$ F8
  ihave F8 := AllocNewCell.memBytes_eq
    (bs' := storeBytes (.i64 (UInt64.ofNat (minOf cb))) 8 ++
      (storeBytes (.i64 (UInt64.ofNat (minOf cb / 2 ^ 64))) 8 ++ (storeBytes (.i64 1) 8 ++ u128Of (minOf cb))))
    (by simp [boundsBytes, u128Of, u128Bytes, minOf]) $$ F8
  icases splitB (a := sp.toNat - 40) (b := sp.toNat - 32) (storeBytes (.i64 (UInt64.ofNat (minOf cb))) 8) _
    (by simp; omega) $$ F8 with ⟨F8, F16⟩
  icases splitB (a := sp.toNat - 32) (b := sp.toNat - 24)
    (storeBytes (.i64 (UInt64.ofNat (minOf cb / 2 ^ 64))) 8) _ (by simp; omega) $$ F16 with ⟨F16, F24⟩
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨O0, O8⟩
  mstep; mstep [F8]; mstep
  mstep; mstep; mstep; mstep; mstep [F16]; mstep [O8]
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 48 + 48 = sp by simp]
  simp only [load_storeBytes_i64]
  ihave O := joinB (a := out.toNat) (b := out.toNat + 8) (storeBytes (.i64 (UInt64.ofNat (minOf cb))) 8) _
    (by simp) $$ [O0 O8]
  · iframe O0 O8
  ihave K := joinB (a := sp.toNat - 32) (b := sp.toNat - 24)
    (storeBytes (.i64 (UInt64.ofNat (minOf cb / 2 ^ 64))) 8) _ (by simp; omega) $$ [F16 F24]
  · iframe F16 F24
  ihave K := joinB (a := sp.toNat - 40) (b := sp.toNat - 32) (storeBytes (.i64 (UInt64.ofNat (minOf cb))) 8) _
    (by simp; omega) $$ [F8 K]
  · iframe F8 K
  ihave K := stkB (b := sp.toNat - 128 + 80 + 8) (k := 40) _ (by omega) (by simp) $$ K
  ihave K := stkJ (a := sp.toNat - 128 + 80) (b := sp.toNat - 128 + 80 + 8) (k1 := 8) (k2 := 40) (k := 48)
    rfl rfl $$ [F0 K]
  · iframe F0 K
  ihave F418 := stkA (b := sp.toNat - 128) (by omega) $$ F418
  ihave K := stkJ (a := sp.toNat - 128) (b := sp.toNat - 128 + 80) (k1 := 80) (k2 := 48) (k := 128)
    rfl rfl $$ [F418 K]
  · iframe F418 K
  ihave C := memBytes_join n (ft.toNat + 16) 8 ((cb.drop 16).take 8) _ (by simp; omega) $$ [C16 C24]
  · iframe C16 C24
  ihave C := memBytes_join n ft.toNat 16 (cb.take 16) _ (by simp; omega) $$ [C0 C]
  · iframe C0 C
  rw [List.take_append_drop, List.take_append_drop]
  isplitl [Hc]
  · iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; rw [hc418]; omega
  iunfold getterPost
  iframe Hg K C
  isplitr
  · ipureintro; rfl
  iapply AllocNewCell.memBytes_eq (by simp [u128Of, u128Bytes]) $$ O

end F230

end WNear.Binary.StorageBalanceBounds
