import Bridge.Functions.StorageWrite
import Bridge.Functions.StateRead
import NearLogic.Hosts.StorageHasKey

/-!
# `env::storage_has_key` through the blockchain interface (551, 436 and 286), `env::state_exists` (552)

```wat
;; 551 storage_has_key(key_ptr, key_len) -> bool
sp -= 16;  [sp+8] := (key_ptr, key_len)          ;; the slice &[u8]
v := call 436(1055020, sp + 8)                    ;; storage_has_key(key)
v > 1 → panic                                     ;; (unreachable: the host returns 0 or 1)
sp += 16;  v as bool

;; 436 LocalKey::with(key, &key_slice) -> u64: as 428 (StorageWrite.lean), the vtable slot 196
;; (index 84), the arguments (data, key_len, key_ptr) as u64

;; 286: local.get 1  local.get 2  call 45   ;; the storage_has_key host
```

* `f286_spec`: the trampoline: 3 instructions and the host's `kh`, for any `ReadContractP` of
  the host (`storageHasKey_readContract` gives one, with `kh = storageHasKeyUse h key kl` and
  the post `StorageHasKeyPost h key st`).
* `f436_spec`: `LocalKey::with` on the installed interface and the `storage_has_key` slot
  (`hslot`, beside `iface`; its code `hCode`): 248 `regular_op_cost`s and the host's gas.
* `f551_spec`: `env::storage_has_key(key) -> bool`: the slice on a 16-byte frame, 436, the
  result `v ∈ {0, 1}` as an `i32`. `f551_spec_host` with `storageHasKey_readContract`: the host
  ends as `StorageHasKeyPost`.
* `f552_spec`: `env::state_exists()`: 551 on the key `"STATE"` at 1056468 (the data segment
  holds it there, `stateKey_data552`). `f552_spec_host` with `storageHasKey_readContract`.
-/

namespace WNear.Binary.StorageHasKey

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-- `storage_has_key`: the table index 84. -/
theorem vtable_storageHasKey : dataWord (1050188 + 196) = bytes32 84 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
theorem wTable_storageHasKey : wTable.elems[84]? = some (Ref.func 286) := rfl

theorem wStore_storageHasKey (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[45]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "storage_has_key" storageHasKeyFn).toHostFn) := by
  simp [wStore, wHosts]

/-! ## The trampoline (286) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (len ptr : UInt64) (key : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 len, .i64 ptr]⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] key)

def trampPost (n : Nat) (Q : NearState → Prop) (ptr : UInt64) (key : List UInt8) (v : UInt64)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h') ∗ n ↦[wms][ ptr.toNat ] key)

/-- `VmBlockchainInterface::storage_has_key` (286, the vtable's index 84):
`storage_has_key(len, ptr)` (import 45) of the key at `ptr`, under any read contract of the
host. -/
theorem f286_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e n a45 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[45]? = some a45)
    (Cg : Nat) (h : NearState) (Q : NearState → Prop) (dp : UInt32) (len ptr v : UInt64)
    (key : List UInt8) (kh : Nat)
    (hc : ReadContractP (metered e "storage_has_key" storageHasKeyFn).toHostFn h Q
      [.i64 len, .i64 ptr] [.i64 v] ptr.toNat key kh Cg) :
    a45 ↪[wf] FuncInst.host (metered e "storage_has_key" storageHasKeyFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f286 Cg (trampPre n h dp len ptr key)
        (fun _ => 3 * cfg.regularOpCost + kh) (trampPost n Q ptr key v) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hb⟩
  subst hargs
  simp only [f286]
  mstep; mstep
  iapply StorageRead.mwpi_call_host_ro_pred' 45 a45 n ptr.toNat _ h Q mx key [.i64 len, .i64 ptr]
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

/-! ## `LocalKey::with` (436), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `storage_has_key` slot of the vtable: offset 196, table index 84, the trampoline 286. -/
def hslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 196 84 (A 286)

/-- The code of `storage_has_key` past `ifaceCode`: the trampoline 286 and the host 45. -/
def hCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 286 ↪[wf] FuncInst.wasm types[3]! inst f286 ∗
    A 45 ↪[wf] FuncInst.host (metered e "storage_has_key" storageHasKeyFn).toHostFn)

instance (e inst : Nat) (A : Nat → Nat) : Persistent (hCode (GF := GF) e inst A) := by
  unfold hCode; infer_instance

theorem hslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 196 ] dataWord (1050188 + 196) ∗ ta ↦[wt][ 84 ] Ref.func (A 286) ⊢
      hslot (GF := GF) n ta A := by
  rw [vtable_storageHasKey]
  iintro ⟨H, T⟩
  iunfold hslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

/-- The key and a pointer to the key slice `(ptr, len)`; the stack pointer, the interface and
its `storage_has_key` slot, the frame below `sp`, the key's bytes and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (key : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 sl]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ hslot n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] key ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (key : List UInt8) (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ hslot n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] key ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxHeartbeats 2000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.storage_has_key(key))` (436) on the
installed interface, under a read contract `hc` of the host (`storageHasKey_readContract`):
248 `regular_op_cost`s and the host's `kh`. -/
theorem f436_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (Q : NearState → Prop) (sl ptr len : UInt32)
    (key : List UInt8) (v : UInt64) (kh : Nat)
    (hc : ReadContractP (metered e "storage_has_key" storageHasKeyFn).toHostFn h Q
      [.i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat)] [.i64 v]
      ptr.toNat key kh Cg)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx ∗ hCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f436 Cg
        (withPre n g ta A gi sp sl ptr len key w0 w4 w8 w12 h)
        (fun _ => 248 * cfg.regularOpCost + kh)
        (withPost n g ta A gi sp sl ptr len key Q v) := by
  iintro ⟨#Hcode, #Hw⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260,
    #F284, #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold hCode at Hw
  icases Hw with ⟨#F286, #H45⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HW, Sp, Sl, HF, Hb, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, ⟨S188, T82⟩⟩
  iunfold hslot, slot at HW
  icases HW with ⟨S196, T84⟩
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
  simp only [f436]
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
      (sp - 16) 1074904 1056436 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056452
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `storage_has_key`
  mstep; mstep [Hda]; mstep; mstep [Sl]; mstep; mstep [Sp]
  simp only [load32u, UInt32.reduceOfNat]
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S196]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 3) (t := 0) (ta := ta) (idx := 84) (a := A 286)
    (type := types[3]!) (inst := inst) (mi := mi) (code := f286)
    [.i32 1, .i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat)])
  isplitr
  · iapply (f286_spec cfg lim (d + 1) types[3]! (by rfl) inst mi e n (A 45) mx hm.mem
      (hm.funcs 45 (by decide)) Cg h Q 1 (UInt64.ofNat len.toNat) (UInt64.ofNat ptr.toNat)
      v key kh (by rw [toNat_ofNat32]; exact hc))
    mpersist
  isplitr
  · iexact F286
  isplitr
  · iexact Hi
  isplitl [T84]
  · simp only [UInt32.reduceToNat]; iexact T84
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
  iintro %rs T84 Hc HQ
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
  ihave HW : hslot (GF := GF) n ta A $$ [S196 T84]
  · iunfold hslot, slot
    simp only [UInt32.reduceToNat, Nat.reduceAdd]
    isplitl [S196]
    · iexact S196
    · iexact T84
  iunfold withPost, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe HW Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 T82 Sp Sl W0 W4 W8 W12 Hb Hhost
  ipureintro; simp [htype]

end With

/-! ## `env::storage_has_key` (551) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.ReadRegister (stk4_word stk_frame4 frame4_stk)

def pre551 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s kp kl : UInt32) (key : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 kp, .i32 kl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ hslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ kp.toNat ] key ∗ mhostPt h)

def post551 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s kp : UInt32) (key : List UInt8)
    (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 v.toUInt32]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ hslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ kp.toNat ] key ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option hygiene false in
/-- The end of 551 on either branch: `sp += 16`, the result, the stack rebuilt. -/
local macro "fin551" : tactic => `(tactic| (
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 16 + 16 = s by simp]
    mstep
    mcredits R
    iframe Hc
    iunfold post551
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
/-- **`env::storage_has_key(key)`** (function 551 of `contract.wasm`) on the installed
interface, for a read contract `hc` of the host returning `v ∈ {0, 1}`
(`storageHasKey_readContract`): returns `v` (whether a value was removed), the host some `h'`
with `Q h'`. -/
theorem f551_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s kp kl : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (key : List UInt8) (h : NearState) (Q : NearState → Prop) (v : UInt64) (hv : v = 0 ∨ v = 1) (kh : Nat)
    (hc : ReadContractP (metered e "storage_has_key" storageHasKeyFn).toHostFn h Q
      [.i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat)] [.i64 v]
      kp.toNat key kh Cg) :
    ifaceCode e inst mi A n mx ∗ hCode e inst A ∗ A 436 ↪[wf] FuncInst.wasm types[30]! inst f436
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f551 Cg (pre551 n g ta A gt s kp kl key h)
        (fun _ => 44 * cfg.regularOpCost + (248 * cfg.regularOpCost + kh))
        (post551 n g ta A gt s kp key Q v) := by
  iintro ⟨#Hcode, #Hw, #F436⟩
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
  iunfold pre551 at HP
  icases HP with ⟨%hargs, Hg, HI, HW, Hs, Hk, Hhost⟩
  subst hargs
  -- the stack: F (16, 436's frame), 8 unused bytes and the slice (8)
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Fr, Hs⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Hs with ⟨M, SK⟩
  rw [show s.toNat - 32 + 16 + 8 = s.toNat - 8 by omega]
  icases VecFromElem.stk_split n (s.toNat - 8) 4 4 $$ SK with ⟨K0, K4⟩
  icases stk4_word n _ $$ K0 with ⟨%x0, K0⟩
  icases stk4_word n _ $$ K4 with ⟨%x4, K4⟩
  icases stk_frame4 n (s.toNat - 32) (s - 16 - 16) e32 $$ Fr with ⟨%w0, %w4, %w8, %w12, Fr⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha436 := hm.funcs 436 (by decide)
  have t30 : types[30]!.params.length = 2 := by rfl
  simp only [f551]
  ihave K0 := memBytes_addr (show s.toNat - 8 = (s - 16).toNat + 8 by omega) $$ K0
  ihave K4 := memBytes_addr (show s.toNat - 8 + 4 = (s - 16).toNat + 12 by omega) $$ K4
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [K4]
  mstep; mstep; mstep [K0]
  have hs16 : 16 ≤ (s - 16).toNat := by omega
  have hal16 : (s - 16).toNat % 8 = 0 := by omega
  have e8' : (s - 16 + 8).toNat = (s - 16).toNat + 8 := by omega
  ihave #HCW : (ifaceCode (GF := GF) e inst mi A n mx ∗ hCode e inst A) $$ []
  · isplitr
    · iexact Hcode
    · iexact Hw
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f436_spec cfg lim (d + 1) types[30]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
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
    fin551
  · mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    simp only [show UInt64.toUInt32 1 = 1 from rfl]
    mstep
    try mpay
    mstep; mstep
    try mpay
    fin551

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `f551_spec` with the host's `storageHasKey_readContract` : the host ends in some
`h'` with `StorageHasKeyPost h key st`, the result is whether `key` has a value, the gas `storageHasKeyUse h key kl`. -/
theorem f551_spec_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s kp kl : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (key : List UInt8) (h : NearState) (st : Near.TrieOverlay.State) {b : Nat}
    (hkl : key.length = kl.toNat) (hkpos : 0 < kl.toNat)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal st (contractKey h.context.currentAccountId key))
    (hproof : ProofBudget h st b)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId key) ≤ b) :
    ifaceCode e inst mi A n mx ∗ hCode e inst A ∗ A 436 ↪[wf] FuncInst.wasm types[30]! inst f436
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f551 Cg (pre551 n g ta A gt s kp kl key h)
        (fun _ => 44 * cfg.regularOpCost + (248 * cfg.regularOpCost + storageHasKeyUse h key kl.toNat))
        (post551 n g ta A gt s kp key (StorageHasKeyPost h key st)
          (StorageRead.foundU64 (h.storage key))) := by
  have hne : ∀ w : UInt32, UInt64.ofNat w.toNat ≠ u64Max := by
    intro w h'
    have := w.toNat_lt
    have h'' := congrArg UInt64.toNat h'
    simp [u64Max] at h''
    omega
  have hc := storageHasKey_readContract (C := Cg) e h (UInt64.ofNat kl.toNat) (UInt64.ofNat kp.toNat)
    key st (hne kl) (by rw [toNat_ofNat32]; exact hkl) (by rw [toNat_ofNat32]; exact hkpos)
    hacc hlim hb hz hlink hproof hbud
  rw [toNat_ofNat32, toNat_ofNat32, StorageRead.storageReadResult_eq] at hc
  have hv : StorageRead.foundU64 (h.storage key) = 0 ∨ StorageRead.foundU64 (h.storage key) = 1 := by
    unfold StorageRead.foundU64; split <;> simp
  exact f551_spec cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s kp kl hs hal key h _ _ hv _ hc

end Spec

/-! ## `env::state_exists` (552)

```wat
;; 552 state_exists() -> bool
i32.const 1056468  i32.const 5  call 551          ;; storage_has_key(b"STATE")
```

The key `"STATE"` is a second copy in the data segment, at 1056468 (`stateKey_data552`).
-/

/-- `"STATE"` is in the data segment at 1056468 too. -/
theorem stateKey_data552 :
    (List.range 5).map (fun k => wNearSource.read (159306 + (1056468 - 1048576) + k)) =
      StateRead.stateKey := by
  decide

section StateExists

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk)

def pre552 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s : UInt32) (h : NearState)
    (args : List Value) : IProp GF :=
  iprop(⌜args = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ hslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ 1056468 ] StateRead.stateKey ∗ mhostPt h)

def post552 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s : UInt32) (Q : NearState → Prop)
    (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 v.toUInt32]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ hslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ 1056468 ] StateRead.stateKey ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxHeartbeats 1000000 in
/-- **`env::state_exists()`** (function 552 of `contract.wasm`): `storage_has_key(b"STATE")`
(551) on the key in the data segment at 1056468, for a read contract `hc` of the host returning
`v ∈ {0, 1}`. -/
theorem f552_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (h : NearState) (Q : NearState → Prop) (v : UInt64) (hv : v = 0 ∨ v = 1) (kh : Nat)
    (hc : ReadContractP (metered e "storage_has_key" storageHasKeyFn).toHostFn h Q
      [.i64 5, .i64 1056468] [.i64 v] 1056468 StateRead.stateKey kh Cg) :
    ifaceCode e inst mi A n mx ∗ hCode e inst A ∗ A 436 ↪[wf] FuncInst.wasm types[30]! inst f436 ∗
      A 551 ↪[wf] FuncInst.wasm types[13]! inst f551
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f552 Cg (pre552 n g ta A gt s h)
        (fun _ => 14 * cfg.regularOpCost + (44 * cfg.regularOpCost + (248 * cfg.regularOpCost + kh)))
        (post552 n g ta A gt s Q v) := by
  iintro ⟨#Hcode, #Hw, #F436, #F551⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre552 at HP
  icases HP with ⟨%hargs, Hg, HI, HW, Hs, Hk, Hhost⟩
  subst hargs
  have ha551 := hm.funcs 551 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  simp only [f552]
  mstep; mstep
  mcall (f551_spec cfg lim (d + 1) types[13]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt s
      1056468 5 hs hal StateRead.stateKey h Q v hv kh (by exact hc)) using [Hg HI HW Hs Hk Hhost]
  · iunfold pre551
    simp only [UInt32.reduceToNat]
    iframe Hg HI HW Hs Hk Hhost
  iunfold post551 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HW, Hs, Hk, Hhost⟩
  subst hrs
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold post552
  iframe Hg HI HW Hs Hk Hhost
  ipureintro; simp [htype]

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `f552_spec` with the host's `storageHasKey_readContract`: the host ends in some `h'` with
`StorageHasKeyPost h stateKey st`, the result is whether `STATE` has a value, the gas
`storageHasKeyUse h stateKey 5`. -/
theorem f552_spec_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (h : NearState) (st : Near.TrieOverlay.State) {b : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage StateRead.stateKey = viewVal st (contractKey h.context.currentAccountId StateRead.stateKey))
    (hproof : ProofBudget h st b)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId StateRead.stateKey) ≤ b) :
    ifaceCode e inst mi A n mx ∗ hCode e inst A ∗ A 436 ↪[wf] FuncInst.wasm types[30]! inst f436 ∗
      A 551 ↪[wf] FuncInst.wasm types[13]! inst f551
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f552 Cg (pre552 n g ta A gt s h)
        (fun _ => 14 * cfg.regularOpCost + (44 * cfg.regularOpCost +
          (248 * cfg.regularOpCost + storageHasKeyUse h StateRead.stateKey 5)))
        (post552 n g ta A gt s (StorageHasKeyPost h StateRead.stateKey st)
          (StorageRead.foundU64 (h.storage StateRead.stateKey))) := by
  have hc := storageHasKey_readContract (C := Cg) e h 5 1056468 StateRead.stateKey st (by decide) (by rfl) (by decide)
    hacc hlim hb hz hlink hproof hbud
  simp only [UInt64.reduceToNat] at hc
  rw [StorageRead.storageReadResult_eq] at hc
  have hv : StorageRead.foundU64 (h.storage StateRead.stateKey) = 0 ∨ StorageRead.foundU64 (h.storage StateRead.stateKey) = 1 := by
    unfold StorageRead.foundU64; split <;> simp
  exact f552_spec cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s hs hal h _ _ hv _ hc

end StateExists


end WNear.Binary.StorageHasKey
