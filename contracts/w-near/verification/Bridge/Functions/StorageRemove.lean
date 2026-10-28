import Bridge.Functions.StorageWrite
import NearLogic.Hosts.StorageRemove

/-!
# `env::storage_remove` through the blockchain interface (549, 439 and 285)

```wat
;; 549 storage_remove(key_ptr, key_len) -> bool
sp -= 16;  [sp+8] := (key_ptr, key_len)          ;; the slice &[u8]
v := call 439(1055020, sp + 8)                    ;; storage_remove(key, EVICTED_REGISTER)
v > 1 → panic                                     ;; (unreachable: the host returns 0 or 1)
sp += 16;  v as bool

;; 439 LocalKey::with(key, &key_slice) -> u64: as 428 (StorageWrite.lean), the vtable slot 192
;; (index 83), the arguments (data, key_len, key_ptr, u64::MAX - 1) as u64

;; 285: local.get 1  local.get 2  local.get 3  call 44   ;; the storage_remove host
```

* `f285_spec`: the trampoline: 4 instructions and the host's `kh`, for any `ReadContractP` of
  the host (`storageRemove_readContract` gives one, with `kh = storageRemoveUse h key kl` and
  the post `StorageRemovePost`).
* `f439_spec`: `LocalKey::with` on the installed interface and the `storage_remove` slot
  (`rslot`, beside `iface`; its code `rCode`): 249 `regular_op_cost`s and the host's gas.
* `f549_spec`: `env::storage_remove(key) -> bool`: the slice on a 16-byte frame, 439, the
  result `v ∈ {0, 1}` as an `i32`. `f549_spec_host` with `storageRemove_readContract`: the host
  ends as `StorageRemovePost` with `EVICTED_REGISTER`.
-/

namespace WNear.Binary.StorageRemove

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.StorageWrite (evictedRegister)

/-- `storage_remove`: the table index 83. -/
theorem vtable_storageRemove : dataWord (1050188 + 192) = bytes32 83 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
theorem wTable_storageRemove : wTable.elems[83]? = some (Ref.func 285) := rfl

theorem wStore_storageRemove (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[44]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "storage_remove" storageRemoveFn).toHostFn) := by
  simp [wStore, wHosts]

/-! ## The trampoline (285) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (len ptr r : UInt64) (key : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 len, .i64 ptr, .i64 r]⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] key)

def trampPost (n : Nat) (Q : NearState → Prop) (ptr : UInt64) (key : List UInt8) (v : UInt64)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h') ∗ n ↦[wms][ ptr.toNat ] key)

/-- `VmBlockchainInterface::storage_remove` (285, the vtable's index 83):
`storage_remove(len, ptr, r)` (import 44) of the key at `ptr`, under any read contract of the
host. -/
theorem f285_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e n a44 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[44]? = some a44)
    (Cg : Nat) (h : NearState) (Q : NearState → Prop) (dp : UInt32) (len ptr r v : UInt64)
    (key : List UInt8) (kh : Nat)
    (hc : ReadContractP (metered e "storage_remove" storageRemoveFn).toHostFn h Q
      [.i64 len, .i64 ptr, .i64 r] [.i64 v] ptr.toNat key kh Cg) :
    a44 ↪[wf] FuncInst.host (metered e "storage_remove" storageRemoveFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f285 Cg (trampPre n h dp len ptr r key)
        (fun _ => 4 * cfg.regularOpCost + kh) (trampPost n Q ptr key v) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hb⟩
  subst hargs
  simp only [f285]
  mstep; mstep; mstep
  iapply StorageRead.mwpi_call_host_ro_pred' 44 a44 n ptr.toNat _ h Q mx key [.i64 len, .i64 ptr, .i64 r]
    [.i64 v] ha hn rfl hc
  iframe Hc Hh Hm Hhost Hb
  isplitr
  · ipureintro; mstep_norm_full; omega
  inext
  iintro %h' %hq Hhost Hb Hc
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold trampPost
  iframe Hb
  isplitr
  · ipureintro; simp [htype]
  iexists h'
  iframe Hhost
  ipureintro; exact hq

end Tramp

/-! ## `LocalKey::with` (439), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `storage_remove` slot of the vtable: offset 192, table index 83, the trampoline 285. -/
def rslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 192 83 (A 285)

/-- The code of `storage_remove` past `ifaceCode`: the trampoline 285 and the host 44. -/
def rCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 285 ↪[wf] FuncInst.wasm types[6]! inst f285 ∗
    A 44 ↪[wf] FuncInst.host (metered e "storage_remove" storageRemoveFn).toHostFn)

instance (e inst : Nat) (A : Nat → Nat) : Persistent (rCode (GF := GF) e inst A) := by
  unfold rCode; infer_instance

theorem rslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 192 ] dataWord (1050188 + 192) ∗ ta ↦[wt][ 83 ] Ref.func (A 285) ⊢
      rslot (GF := GF) n ta A := by
  rw [vtable_storageRemove]
  iintro ⟨H, T⟩
  iunfold rslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

/-- The key and a pointer to the key slice `(ptr, len)`; the stack pointer, the interface and
its `storage_remove` slot, the frame below `sp`, the key's bytes and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (key : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 sl]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ rslot n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] key ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (key : List UInt8) (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ rslot n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] key ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxHeartbeats 2000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.storage_remove(key, EVICTED_REGISTER))` (439) on the
installed interface, under a read contract `hc` of the host (`storageRemove_readContract`):
249 `regular_op_cost`s and the host's `kh`. -/
theorem f439_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (Q : NearState → Prop) (sl ptr len : UInt32)
    (key : List UInt8) (v : UInt64) (kh : Nat)
    (hc : ReadContractP (metered e "storage_remove" storageRemoveFn).toHostFn h Q
      [.i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat), .i64 evictedRegister] [.i64 v]
      ptr.toNat key kh Cg)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx ∗ rCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f439 Cg
        (withPre n g ta A gi sp sl ptr len key w0 w4 w8 w12 h)
        (fun _ => 249 * cfg.regularOpCost + kh)
        (withPost n g ta A gi sp sl ptr len key Q v) := by
  iintro ⟨#Hcode, #Hw⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260,
    #F284, #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold rCode at Hw
  icases Hw with ⟨#F285, #H44⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HW, Sp, Sl, HF, Hb, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, ⟨S188, T82⟩⟩
  iunfold rslot, slot at HW
  icases HW with ⟨S192, T83⟩
  iunfold frame4 at HF
  icases HF with ⟨W0, W4, W8, W12⟩
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e12 : (sp - 16 + 12).toNat = (sp - 16).toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hor : (sp - 16 + 8) ||| 4 = sp - 16 + 12 := or_four _ (by omega) (by omega)
  have hg := hm.glob
  have hn := hm.mem
  have ha429 := hm.funcs 429 (by decide)
  have ha430 := hm.funcs 430 (by decide)
  have ha431 := hm.funcs 431 (by decide)
  have ha432 := hm.funcs 432 (by decide)
  have t429 : types[31]!.params.length = 3 := by rfl
  have t430 : types[13]!.params.length = 2 := by rfl
  have t431 : types[0]!.params.length = 1 := by rfl
  have t432 : types[24]!.params.length = 2 := by rfl
  simp only [f439]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mstep; mstep [Hkey]
  -- `__getit` through the table
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 1) (t := 0) (ta := ta) (idx := 116) (a := A 565)
    (type := types[1]!) (inst := inst) (mi := mi) (code := f565) [])
  isplitr
  · iapply (Borrow.f565_spec cfg lim (d + 1) types[1]! (by rfl) inst mi n (A 468) hm.mem
      (hm.funcs 468 (by decide)) types[13]! (by rfl) (by rfl) (by omega) Cg)
    mpersist
  isplitr
  · iexact F565
  isplitr
  · iexact Hi
  isplitl [T116]
  · simp only [UInt32.reduceToNat]; iexact T116
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hst]
  · iunfold Borrow.getItPre
    iframe Hst
    ipureintro; rfl
  inext
  iintro %rs T116 Hc HQ
  iunfold Borrow.getItPost at HQ
  icases HQ with ⟨%hrs, Hst⟩
  subst hrs
  mctrl_norm
  -- not null
  mstep; mstep; mstep
  -- `RefCell::borrow`
  mstep; mstep; mstep
  mcall (Borrow.f429_spec cfg lim (d + 1) types[31]! (by rfl) inst mi n g (A 494) (A 672) hm.mem
      hm.glob (hm.funcs 494 (by decide)) (hm.funcs 672 (by decide)) types[32]! types[13]! (by rfl)
      (by rfl) (by rfl) (by rfl) (by omega) Cg { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl
      (sp - 16) 1074904 1056388 w0 w4 (by decide)) using [Hg Hfl W0 W4]
  · iunfold Borrow.borrowPre
    simp only [UInt32.reduceToNat]
    iframe Hg Hfl W0 W4
  iunfold Borrow.borrowPost at HQ
  icases HQ with ⟨%hrs, Hg, Hfl, W0, W4⟩
  subst hrs
  simp only [UInt32.reduceToNat, UInt32.reduceAdd]
  -- the `Ref` copied
  mstep; mstep; mstep [W4]; mstep [W12]
  mstep; mstep; mstep [W0]; mstep; mstep [W8]
  -- `Some`: the box
  try simp only [UInt32.reduceOfNat]
  mstep; mstep
  try simp only [UInt32.reduceOfNat]
  mstep
  mstep [Hda]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply Borrow.mwpi_select_true'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨by mstep_norm_full; omega, by decide⟩
  inext
  iintro Hc
  mctrl_norm
  mstep
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056404
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `storage_remove`
  mstep; mstep [Hda]; mstep; mstep [Sl]; mstep; mstep [Sp]
  simp only [load32u, UInt32.reduceOfNat]
  mstep
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S192]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 6) (t := 0) (ta := ta) (idx := 83) (a := A 285)
    (type := types[6]!) (inst := inst) (mi := mi) (code := f285)
    [.i32 1, .i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat), .i64 evictedRegister])
  isplitr
  · iapply (f285_spec cfg lim (d + 1) types[6]! (by rfl) inst mi e n (A 44) mx hm.mem
      (hm.funcs 44 (by decide)) Cg h Q 1 (UInt64.ofNat len.toNat) (UInt64.ofNat ptr.toNat)
      evictedRegister v key kh (by rw [toNat_ofNat32]; exact hc))
    mpersist
  isplitr
  · iexact F285
  isplitr
  · iexact Hi
  isplitl [T83]
  · simp only [UInt32.reduceToNat]; iexact T83
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hhost Hb]
  · iunfold trampPre
    rw [toNat_ofNat32]
    iframe Hhost Hb
    ipureintro; rfl
  inext
  iintro %rs T83 Hc HQ
  iunfold trampPost at HQ
  icases HQ with ⟨%hrs, Hhost, Hb⟩
  subst hrs
  mctrl_norm
  mstep
  -- the `Ref` dropped
  mstep; mstep; mstep; mstep; mstep
  rw [hor]
  mcall (Borrow.f431_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n (A 672) hm.mem
      (hm.funcs 672 (by decide)) types[13]! (by rfl) (by rfl) (by omega) Cg (sp - 16 + 12) 1074904 1)
    using [W12 Hfl]
  · iunfold Borrow.dropPre
    rw [e12]
    simp only [UInt32.reduceToNat]
    iframe W12 Hfl
  iunfold Borrow.dropPost at HQ
  icases HQ with ⟨%hrs, W12, Hfl⟩
  subst hrs
  rw [e12]
  simp only [UInt32.reduceToNat, UInt32.reduceAdd]
  mstep; mstep; mstep
  -- `Result::expect`
  mstep; mstep
  mcall (Borrow.f432_spec cfg lim (d + 1) types[24]! (by rfl) inst mi g hm.glob Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl v) using [Hg]
  · iunfold Borrow.resultPre
    iframe Hg
    ipureintro; rfl
  iunfold Borrow.resultPost at HQ
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  -- sp += 16
  mstep; mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  mstep
  rw [toNat_ofNat32]
  mcredits R
  iframe Hc
  ihave HW : rslot (GF := GF) n ta A $$ [S192 T83]
  · iunfold rslot, slot
    simp only [UInt32.reduceToNat, Nat.reduceAdd]
    isplitl [S192]
    · iexact S192
    · iexact T83
  iunfold withPost, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe HW Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 T82 Sp Sl W0 W4 W8 W12 Hb Hhost
  ipureintro; simp [htype]

end With

/-! ## `env::storage_remove` (549) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.ReadRegister (stk4_word stk_frame4 frame4_stk)

def pre549 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s kp kl : UInt32) (key : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 kp, .i32 kl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ rslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ kp.toNat ] key ∗ mhostPt h)

def post549 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s kp : UInt32) (key : List UInt8)
    (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 v.toUInt32]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ rslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ kp.toNat ] key ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option hygiene false in
/-- The end of 549 on either branch: `sp += 16`, the result, the stack rebuilt. -/
local macro "fin549" : tactic => `(tactic| (
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 16 + 16 = s by simp]
    mstep
    mcredits R
    iframe Hc
    iunfold post549
    isplitr
    · ipureintro; simp only [htype, Nat.sub_self, List.drop_zero]; rfl
    iframe Hg HI HW Hk
    isplitr [Hhost]
    · ihave Fr := frame4_stk n (s.toNat - 32) _ e32 _ _ _ _ $$ Fr
      ihave K0 := stk_word n _ _ $$ K0
      ihave K4 := stk_word n _ _ $$ K4
      ihave K := stk_join n _ 4 4 $$ [K0 K4]
      · rw [show (s - 16).toNat + 8 + 4 = (s - 16).toNat + 12 by omega]; iframe K0 K4
      ihave K := stk_addr (show (s - 16).toNat + 8 = s.toNat - 32 + 16 + 8 by omega) $$ K
      ihave MK := stk_join n _ 8 8 $$ [M K]
      · iframe M K
      iapply stk_join n (s.toNat - 32) 16 16
      iframe Fr MK
    iexists h'
    iframe Hhost
    ipureintro; exact hq))

set_option maxHeartbeats 4000000 in
/-- **`env::storage_remove(key)`** (function 549 of `contract.wasm`) on the installed
interface, for a read contract `hc` of the host returning `v ∈ {0, 1}`
(`storageRemove_readContract`): returns `v` (whether a value was removed), the host some `h'`
with `Q h'`. -/
theorem f549_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s kp kl : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (key : List UInt8) (h : NearState) (Q : NearState → Prop) (v : UInt64) (hv : v = 0 ∨ v = 1) (kh : Nat)
    (hc : ReadContractP (metered e "storage_remove" storageRemoveFn).toHostFn h Q
      [.i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat), .i64 evictedRegister] [.i64 v]
      kp.toNat key kh Cg) :
    ifaceCode e inst mi A n mx ∗ rCode e inst A ∗ A 439 ↪[wf] FuncInst.wasm types[30]! inst f439
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f549 Cg (pre549 n g ta A gt s kp kl key h)
        (fun _ => 44 * cfg.regularOpCost + (249 * cfg.regularOpCost + kh))
        (post549 n g ta A gt s kp key Q v) := by
  iintro ⟨#Hcode, #Hw, #F439⟩
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h16]; omega
  have e32 : (s - 16 - 16).toNat = s.toNat - 32 := by
    have h1 : (16 : UInt32) ≤ s - 16 := by rw [UInt32.le_iff_toNat_le, h16]; simp; omega
    rw [UInt32.toNat_sub_of_le _ _ h1, h16]; simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre549 at HP
  icases HP with ⟨%hargs, Hg, HI, HW, Hs, Hk, Hhost⟩
  subst hargs
  -- the stack: F (16, 439's frame), 8 unused bytes and the slice (8)
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Fr, Hs⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Hs with ⟨M, SK⟩
  rw [show s.toNat - 32 + 16 + 8 = s.toNat - 8 by omega]
  icases VecFromElem.stk_split n (s.toNat - 8) 4 4 $$ SK with ⟨K0, K4⟩
  icases stk4_word n _ $$ K0 with ⟨%x0, K0⟩
  icases stk4_word n _ $$ K4 with ⟨%x4, K4⟩
  icases stk_frame4 n (s.toNat - 32) (s - 16 - 16) e32 $$ Fr with ⟨%w0, %w4, %w8, %w12, Fr⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha439 := hm.funcs 439 (by decide)
  have t30 : types[30]!.params.length = 2 := by rfl
  simp only [f549]
  ihave K0 := memBytes_addr (show s.toNat - 8 = (s - 16).toNat + 8 by omega) $$ K0
  ihave K4 := memBytes_addr (show s.toNat - 8 + 4 = (s - 16).toNat + 12 by omega) $$ K4
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [K4]
  mstep; mstep; mstep [K0]
  have hs16 : 16 ≤ (s - 16).toNat := by omega
  have hal16 : (s - 16).toNat % 8 = 0 := by omega
  have e8' : (s - 16 + 8).toNat = (s - 16).toNat + 8 := by omega
  ihave #HCW : (ifaceCode (GF := GF) e inst mi A n mx ∗ rCode e inst A) $$ []
  · isplitr
    · iexact Hcode
    · iexact Hw
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f439_spec cfg lim (d + 1) types[30]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 16)⟩ (s - 16) rfl hs16 hal16 h Q (s - 16 + 8) kp kl key v kh hc
      w0 w4 w8 w12) using [Hg HI HW K0 K4 Fr Hk Hhost]
  · iunfold withPre
    ihave K0 := memBytes_addr (show (s - 16).toNat + 8 = (s - 16 + 8).toNat by omega) $$ K0
    ihave K4 := memBytes_addr (show (s - 16).toNat + 12 = (s - 16 + 8).toNat + 4 by omega) $$ K4
    iframe Hg HI HW K0 K4 Fr Hk Hhost
    ipureintro; rfl
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, HW, K0, K4, Fr, Hk, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  ihave K0 := memBytes_addr e8' $$ K0
  ihave K4 := memBytes_addr (show (s - 16 + 8).toNat + 4 = (s - 16).toNat + 12 by omega) $$ K4
  rcases hv with rfl | rfl
  · mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    simp only [show UInt64.toUInt32 0 = 0 from rfl]
    mstep
    try mpay
    fin549
  · mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    simp only [show UInt64.toUInt32 1 = 1 from rfl]
    mstep
    try mpay
    mstep; mstep
    try mpay
    fin549

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `f549_spec` with the host's `storageRemove_readContract` (register `EVICTED_REGISTER`): the
host ends in some `h'` with `StorageRemovePost e h key evictedRegister st`, the result is whether
`key` had a value, the gas `storageRemoveUse h key kl`. -/
theorem f549_spec_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s kp kl : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (key : List UInt8) (h : NearState) (st : Near.TrieOverlay.State) {b : Nat}
    (hkl : key.length = kl.toNat) (hkpos : 0 < kl.toNat)
    (hview : h.context.isView = false)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal st (contractKey h.context.currentAccountId key))
    (hproof : ProofBudget h st b)
    (hbud : removeProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ b)
    (hreg : ∀ v, h.storage key = some v → withinLimit h.config.maxRegisterLen v.length = true) :
    ifaceCode e inst mi A n mx ∗ rCode e inst A ∗ A 439 ↪[wf] FuncInst.wasm types[30]! inst f439
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f549 Cg (pre549 n g ta A gt s kp kl key h)
        (fun _ => 44 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageRemoveUse h key kl.toNat))
        (post549 n g ta A gt s kp key (StorageRemovePost e h key evictedRegister st)
          (StorageRead.foundU64 (h.storage key))) := by
  have hne : ∀ w : UInt32, UInt64.ofNat w.toNat ≠ u64Max := by
    intro w h'
    have := w.toNat_lt
    have h'' := congrArg UInt64.toNat h'
    simp [u64Max] at h''
    omega
  have hc := storageRemove_readContract (C := Cg) e h (UInt64.ofNat kl.toNat) (UInt64.ofNat kp.toNat)
    evictedRegister key st (hne kl) (by rw [toNat_ofNat32]; exact hkl) (by rw [toNat_ofNat32]; exact hkpos)
    hview hacc hlim hb hz hlink hproof hbud (fun v hv _ => hreg v hv)
  rw [toNat_ofNat32, toNat_ofNat32, StorageRead.storageReadResult_eq] at hc
  have hv : StorageRead.foundU64 (h.storage key) = 0 ∨ StorageRead.foundU64 (h.storage key) = 1 := by
    unfold StorageRead.foundU64; split <;> simp
  exact f549_spec cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s kp kl hs hal key h _ _ hv _ hc

end Spec

end WNear.Binary.StorageRemove
