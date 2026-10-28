import Bridge.Functions.StorageReadWrap
import NearLogic.CallPred2
import NearLogic.Hosts.StorageWrite

/-!
# `storage_write` through the blockchain interface (428 and 283)

`env::storage_write(key, value)` (547) calls

```wat
;; 428 LocalKey::with(key, &key_slice, &value_slice) -> u64: as 459 (StorageRead.lean), the
;; vtable slot 184 (index 81), the arguments (data, key_len, key_ptr, value_len, value_ptr,
;; u64::MAX - 1) as u64 (near-sdk's EVICTED_REGISTER)

;; 283: local.get 1 .. local.get 5  call 42   ;; the storage_write host
```

* `f283_spec`: the trampoline: 6 instructions and the host's `kh`, for any
  `ReadContractP2` of the host (`storageWrite_readContract` gives one, with
  `kh = storageWriteUse h key kl vl` and the post `StorageWritePost`).
* `f428_spec`: `LocalKey::with` on the installed interface and the `storage_write` slot (`wslot`,
  beside `iface`; its code `wCode`): 257 `regular_op_cost`s and the host's gas; the host's result
  (`v`, 1 evicted / 0 not) returned.
* `f547_spec`: `env::storage_write(key, value) -> bool` (547): the two slices on a 16-byte frame,
  428, the result `v ∈ {0, 1}` as an `i32`: 51 `regular_op_cost`s more. `f547_spec_host` with
  `storageWrite_readContract`: the host ends as `StorageWritePost` with `EVICTED_REGISTER`.
-/

namespace WNear.Binary.StorageWrite

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-- near-sdk's `EVICTED_REGISTER`, `u64::MAX - 1`: where `storage_write` puts the old value. -/
def evictedRegister : UInt64 := 18446744073709551614

theorem evictedRegister_ne : evictedRegister ≠ u64Max := by decide

/-- `storage_write`: the table index 81. -/
theorem vtable_storageWrite : dataWord (1050188 + 184) = bytes32 81 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
theorem wTable_storageWrite : wTable.elems[81]? = some (Ref.func 283) := rfl

theorem wStore_storageWrite (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[42]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn) := by
  simp [wStore, wHosts]

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}
  {Cg K : Nat}

/-- `mwpi_call_host_ro_pred2` on a stack holding just the arguments, the credits any `K`
covering the call and the host's gas. -/
theorem mwpi_call_host_ro_pred2' (i a n p1 p2 : Nat) (fn : HostFn NearState) (h : NearState)
    (Q : NearState → Prop) (mx : Option Nat) (b1 b2 : List UInt8) (args rs : List Value) {kh : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length)
    (hd : p1 + b1.length ≤ p2 ∨ p2 + b2.length ≤ p1)
    (hc : ReadContractP2 fn h Q args rs p1 b1 p2 b2 kh Cg) :
    credits Cg K ∗ ⌜cfg.regularOpCost + kh ≤ K⌝ ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗
      mhostPt h ∗ n ↦[wms][ p1 ] b1 ∗ n ↦[wms][ p2 ] b2 ∗
      ▷ (∀ h', ⌜Q h'⌝ -∗ mhostPt h' -∗ n ↦[wms][ p1 ] b1 -∗ n ↦[wms][ p2 ] b2 -∗
        credits Cg (K - (cfg.regularOpCost + kh)) -∗ Φ.normal rs f)
      ⊢ mwpi cfg lim d f args [.call i] Φ := by
  iintro ⟨Hc, %hK, Hf, Hm, Hh, Hb1, Hb2, H⟩
  have r := mwpi_call_host_ro_pred2 (cfg := cfg) (lim := lim) (d := d) (f := f) (Φ := Φ)
    (R := K - (cfg.regularOpCost + kh)) i a n p1 p2 fn h Q mx b1 b2 [] args rs ha hn hlen hd hc
  simp only [List.nil_append] at r
  iapply r
  rw [show cfg.regularOpCost + kh + (K - (cfg.regularOpCost + kh)) = K by omega]
  iframe Hc Hf Hm Hh Hb1 Hb2 H

end Flex

/-! ## The trampoline (283) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (kl kp vl vp r : UInt64) (key val : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r]⌝ ∗ mhostPt h ∗
    n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val)

def trampPost (n : Nat) (Q : NearState → Prop) (kp vp : UInt64) (key val : List UInt8) (v : UInt64)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h') ∗ n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val)

/-- `VmBlockchainInterface::storage_write` (283, the vtable's index 81):
`storage_write(kl, kp, vl, vp, r)` (import 42), under any two-range read contract of the host. -/
theorem f283_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e n a42 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[42]? = some a42)
    (Cg : Nat) (h : NearState) (Q : NearState → Prop) (dp : UInt32) (kl kp vl vp r v : UInt64)
    (key val : List UInt8) (kh : Nat) (hd : kp.toNat + key.length ≤ vp.toNat ∨ vp.toNat + val.length ≤ kp.toNat)
    (hc : ReadContractP2 (metered e "storage_write" storageWriteFn).toHostFn h Q
      [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] [.i64 v] kp.toNat key vp.toNat val kh Cg) :
    a42 ↪[wf] FuncInst.host (metered e "storage_write" storageWriteFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f283 Cg (trampPre n h dp kl kp vl vp r key val)
        (fun _ => 6 * cfg.regularOpCost + kh) (trampPost n Q kp vp key val v) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hk, Hv⟩
  subst hargs
  simp only [f283]
  mstep; mstep; mstep; mstep; mstep
  iapply mwpi_call_host_ro_pred2' 42 a42 n kp.toNat vp.toNat _ h Q mx key val
    [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] [.i64 v] ha hn rfl hd hc
  iframe Hc Hh Hm Hhost Hk Hv
  isplitr
  · ipureintro; omega
  inext
  iintro %h' %hq Hhost Hk Hv Hc
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold trampPost
  iframe Hk Hv
  isplitr
  · ipureintro; simp [htype]
  iexists h'
  iframe Hhost
  ipureintro; exact hq

end Tramp

/-! ## `LocalKey::with` (428), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `storage_write` slot of the vtable: offset 184, table index 81, the trampoline 283. -/
def wslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 184 81 (A 283)

/-- The code of `storage_write` past `ifaceCode`: the trampoline 283 and the host 42. -/
def wCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 283 ↪[wf] FuncInst.wasm types[2]! inst f283 ∗
    A 42 ↪[wf] FuncInst.host (metered e "storage_write" storageWriteFn).toHostFn)

instance (e inst : Nat) (A : Nat → Nat) : Persistent (wCode (GF := GF) e inst A) := by
  unfold wCode; infer_instance

theorem wslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 184 ] dataWord (1050188 + 184) ∗ ta ↦[wt][ 81 ] Ref.func (A 283) ⊢
      wslot (GF := GF) n ta A := by
  rw [vtable_storageWrite]
  iintro ⟨H, T⟩
  iunfold wslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

/-- The key, the key slice `(kp, kl)` at `sk` and the value slice `(vp, vl)` at `sv`; the stack
pointer, the interface and its `storage_write` slot, the frame below `sp`, the bytes and the
host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sk sv kp kl vp vl : UInt32)
    (key val : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 sk, .i32 sv]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ wslot n ta A ∗
    n ↦[i32][ sk.toNat ] kp ∗ n ↦[i32][ sk.toNat + 4 ] kl ∗
    n ↦[i32][ sv.toNat ] vp ∗ n ↦[i32][ sv.toNat + 4 ] vl ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sk sv kp kl vp vl : UInt32)
    (key val : List UInt8) (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ wslot n ta A ∗
    n ↦[i32][ sk.toNat ] kp ∗ n ↦[i32][ sk.toNat + 4 ] kl ∗
    n ↦[i32][ sv.toNat ] vp ∗ n ↦[i32][ sv.toNat + 4 ] vl ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ kp.toNat ] key ∗
    n ↦[wms][ vp.toNat ] val ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxHeartbeats 2000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.storage_write(key, value, EVICTED_REGISTER))` (428) on the
installed interface, under a two-range read contract `hc` of the host
(`storageWrite_readContract`): 257 `regular_op_cost`s and the host's `kh`. -/
theorem f428_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (Q : NearState → Prop) (sk sv kp kl vp vl : UInt32)
    (key val : List UInt8) (v : UInt64) (kh : Nat)
    (hdj : kp.toNat + key.length ≤ vp.toNat ∨ vp.toNat + val.length ≤ kp.toNat)
    (hc : ReadContractP2 (metered e "storage_write" storageWriteFn).toHostFn h Q
      [.i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat), .i64 (UInt64.ofNat vl.toNat),
        .i64 (UInt64.ofNat vp.toNat), .i64 evictedRegister] [.i64 v] kp.toNat key vp.toNat val kh Cg)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx ∗ wCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f428 Cg
        (withPre n g ta A gi sp sk sv kp kl vp vl key val w0 w4 w8 w12 h)
        (fun _ => 257 * cfg.regularOpCost + kh)
        (withPost n g ta A gi sp sk sv kp kl vp vl key val Q v) := by
  iintro ⟨#Hcode, #Hw⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260,
    #F284, #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold wCode at Hw
  icases Hw with ⟨#F283, #H42⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HW, K0, K4, V0, V4, HF, Hk, Hv, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, ⟨S188, T82⟩⟩
  iunfold wslot, slot at HW
  icases HW with ⟨S184, T81⟩
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
  simp only [f428]
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
      (sp - 16) 1074904 1056276 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056292
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `storage_write`
  mstep; mstep [Hda]; mstep; mstep [K4]; mstep; mstep [K0]
  mstep; mstep [V4]; mstep; mstep [V0]
  simp only [load32u, UInt32.reduceOfNat]
  mstep
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S184]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 2) (t := 0) (ta := ta) (idx := 81) (a := A 283)
    (type := types[2]!) (inst := inst) (mi := mi) (code := f283)
    [.i32 1, .i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat), .i64 (UInt64.ofNat vl.toNat),
      .i64 (UInt64.ofNat vp.toNat), .i64 evictedRegister])
  isplitr
  · iapply (f283_spec cfg lim (d + 1) types[2]! (by rfl) inst mi e n (A 42) mx hm.mem
      (hm.funcs 42 (by decide)) Cg h Q 1 (UInt64.ofNat kl.toNat) (UInt64.ofNat kp.toNat)
      (UInt64.ofNat vl.toNat) (UInt64.ofNat vp.toNat) evictedRegister v key val kh
      (by rw [toNat_ofNat32, toNat_ofNat32]; exact hdj)
      (by rw [toNat_ofNat32, toNat_ofNat32]; exact hc))
    mpersist
  isplitr
  · iexact F283
  isplitr
  · iexact Hi
  isplitl [T81]
  · simp only [UInt32.reduceToNat]; iexact T81
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hhost Hk Hv]
  · iunfold trampPre
    rw [toNat_ofNat32, toNat_ofNat32]
    iframe Hhost Hk Hv
    ipureintro; rfl
  inext
  iintro %rs T81 Hc HQ
  iunfold trampPost at HQ
  icases HQ with ⟨%hrs, Hhost, Hk, Hv⟩
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
  rw [toNat_ofNat32, toNat_ofNat32]
  mcredits R
  iframe Hc
  ihave HW : wslot (GF := GF) n ta A $$ [S184 T81]
  · iunfold wslot, slot
    simp only [UInt32.reduceToNat, Nat.reduceAdd]
    isplitl [S184]
    · iexact S184
    · iexact T81
  iunfold withPost, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe HW Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 T82 K0 K4 V0 V4 W0 W4 W8 W12 Hk Hv Hhost
  ipureintro; simp [htype]

end With

/-! ## `env::storage_write` (547) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.ReadRegister (stk4_word stk_frame4 frame4_stk)

def pre547 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s kp kl vp vl : UInt32) (key val : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 kp, .i32 kl, .i32 vp, .i32 vl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ wslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val ∗ mhostPt h)

def post547 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s kp vp : UInt32) (key val : List UInt8)
    (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 v.toUInt32]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ wslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ vp.toNat ] val ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option hygiene false in
/-- The end of 547 on either branch: `sp += 16`, the result, the stack rebuilt. -/
local macro "fin547" : tactic => `(tactic| (
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 16 + 16 = s by simp]
    mstep
    mcredits R
    iframe Hc
    iunfold post547
    isplitr
    · ipureintro; simp only [htype, Nat.sub_self, List.drop_zero]; rfl
    iframe Hg HI HW Hk Hv
    isplitr [Hhost]
    · ihave Fr := frame4_stk n (s.toNat - 32) _ e32 _ _ _ _ $$ Fr
      ihave K0 := stk_word n _ _ $$ K0
      ihave K4 := stk_word n _ _ $$ K4
      ihave V0 := stk_word n _ _ $$ V0
      ihave V4 := stk_word n _ _ $$ V4
      ihave K := stk_join n _ 4 4 $$ [K0 K4]
      · iframe K0 K4
      ihave V := stk_join n _ 4 4 $$ [V0 V4]
      · rw [show (s - 16).toNat + 8 + 4 = (s - 16).toNat + 12 by omega]; iframe V0 V4
      ihave KV := stk_join n _ 8 8 $$ [K V]
      · iframe K V
      ihave KV := stk_addr (show (s - 16).toNat = s.toNat - 32 + 16 by omega) $$ KV
      iapply stk_join n (s.toNat - 32) 16 16
      iframe Fr KV
    iexists h'
    iframe Hhost
    ipureintro; exact hq))

set_option maxHeartbeats 4000000 in
/-- **`env::storage_write(key, value)`** (function 547 of `contract.wasm`) on the installed
interface, for a two-range read contract `hc` of the host returning `v ∈ {0, 1}`
(`storageWrite_readContract`): returns `v` (whether a value was evicted), the host some `h'` with
`Q h'`. -/
theorem f547_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s kp kl vp vl : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (key val : List UInt8) (h : NearState) (Q : NearState → Prop) (v : UInt64) (hv : v = 0 ∨ v = 1) (kh : Nat)
    (hdj : kp.toNat + key.length ≤ vp.toNat ∨ vp.toNat + val.length ≤ kp.toNat)
    (hc : ReadContractP2 (metered e "storage_write" storageWriteFn).toHostFn h Q
      [.i64 (UInt64.ofNat kl.toNat), .i64 (UInt64.ofNat kp.toNat), .i64 (UInt64.ofNat vl.toNat),
        .i64 (UInt64.ofNat vp.toNat), .i64 evictedRegister] [.i64 v] kp.toNat key vp.toNat val kh Cg) :
    ifaceCode e inst mi A n mx ∗ wCode e inst A ∗ A 428 ↪[wf] FuncInst.wasm types[54]! inst f428
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f547 Cg (pre547 n g ta A gt s kp kl vp vl key val h)
        (fun _ => 51 * cfg.regularOpCost + (257 * cfg.regularOpCost + kh))
        (post547 n g ta A gt s kp vp key val Q v) := by
  iintro ⟨#Hcode, #Hw, #F428⟩
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
  iunfold pre547 at HP
  icases HP with ⟨%hargs, Hg, HI, HW, Hs, Hk, Hv, Hhost⟩
  subst hargs
  -- the stack: F (16, 428's frame) and the two slices (8 + 8)
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Fr, Hs⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Hs with ⟨SK, SV⟩
  rw [show s.toNat - 32 + 16 = s.toNat - 16 by omega, show s.toNat - 16 + 8 = s.toNat - 8 by omega]
  icases VecFromElem.stk_split n (s.toNat - 16) 4 4 $$ SK with ⟨K0, K4⟩
  icases VecFromElem.stk_split n (s.toNat - 8) 4 4 $$ SV with ⟨V0, V4⟩
  icases stk4_word n _ $$ K0 with ⟨%x0, K0⟩
  icases stk4_word n _ $$ K4 with ⟨%x4, K4⟩
  icases stk4_word n _ $$ V0 with ⟨%y0, V0⟩
  icases stk4_word n _ $$ V4 with ⟨%y4, V4⟩
  icases stk_frame4 n (s.toNat - 32) (s - 16 - 16) e32 $$ Fr with ⟨%w0, %w4, %w8, %w12, Fr⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha428 := hm.funcs 428 (by decide)
  have t54 : types[54]!.params.length = 3 := by rfl
  simp only [f547]
  ihave K0 := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ K0
  ihave K4 := memBytes_addr (show s.toNat - 16 + 4 = (s - 16).toNat + 4 by omega) $$ K4
  ihave V0 := memBytes_addr (show s.toNat - 8 = (s - 16).toNat + 8 by omega) $$ V0
  ihave V4 := memBytes_addr (show s.toNat - 8 + 4 = (s - 16).toNat + 12 by omega) $$ V4
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [K4]
  mstep; mstep; mstep [K0]
  mstep; mstep; mstep [V4]
  mstep; mstep; mstep [V0]
  have hs16 : 16 ≤ (s - 16).toNat := by omega
  have hal16 : (s - 16).toNat % 8 = 0 := by omega
  have e8' : (s - 16 + 8).toNat = (s - 16).toNat + 8 := by omega
  ihave #HCW : (ifaceCode (GF := GF) e inst mi A n mx ∗ wCode e inst A) $$ []
  · isplitr
    · iexact Hcode
    · iexact Hw
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f428_spec cfg lim (d + 1) types[54]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 16)⟩ (s - 16) rfl hs16 hal16 h Q (s - 16) (s - 16 + 8) kp kl vp vl key val v kh hdj hc
      w0 w4 w8 w12) using [Hg HI HW K0 K4 V0 V4 Fr Hk Hv Hhost]
  · iunfold withPre
    ihave V0 := memBytes_addr (show (s - 16).toNat + 8 = (s - 16 + 8).toNat by omega) $$ V0
    ihave V4 := memBytes_addr (show (s - 16).toNat + 12 = (s - 16 + 8).toNat + 4 by omega) $$ V4
    iframe Hg HI HW K0 K4 V0 V4 Fr Hk Hv Hhost
    ipureintro; rfl
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, HW, K0, K4, V0, V4, Fr, Hk, Hv, ⟨%h', %hq, Hhost⟩⟩
  subst hrs
  ihave V0 := memBytes_addr e8' $$ V0
  ihave V4 := memBytes_addr (show (s - 16 + 8).toNat + 4 = (s - 16).toNat + 12 by omega) $$ V4
  rcases hv with rfl | rfl
  · mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    simp only [show UInt64.toUInt32 0 = 0 from rfl]
    mstep
    try mpay
    fin547
  · mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    simp only [show UInt64.toUInt32 1 = 1 from rfl]
    mstep
    try mpay
    mstep; mstep
    try mpay
    fin547

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- `f547_spec` with the host's `storageWrite_readContract` (register `EVICTED_REGISTER`): the
host ends in some `h'` with `StorageWritePost e h key val evictedRegister st`, the result is
whether `key` had a value, the gas `storageWriteUse h key kl vl`. -/
theorem f547_spec_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s kp kl vp vl : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (key val : List UInt8) (h : NearState) (st : Near.TrieOverlay.State) {b : Nat}
    (hkl : key.length = kl.toNat) (hkpos : 0 < kl.toNat) (hvl : val.length = vl.toNat) (hvpos : 0 < vl.toNat)
    (hdj : kp.toNat + key.length ≤ vp.toNat ∨ vp.toNat + val.length ≤ kp.toNat)
    (hview : h.context.isView = false)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen val.length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal st (contractKey h.context.currentAccountId key))
    (hproof : ProofBudget h st b)
    (hbud : writeProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ b)
    (hreg : ∀ v, h.storage key = some v → withinLimit h.config.maxRegisterLen v.length = true) :
    ifaceCode e inst mi A n mx ∗ wCode e inst A ∗ A 428 ↪[wf] FuncInst.wasm types[54]! inst f428
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f547 Cg (pre547 n g ta A gt s kp kl vp vl key val h)
        (fun _ => 51 * cfg.regularOpCost + (257 * cfg.regularOpCost + storageWriteUse h key kl.toNat vl.toNat))
        (post547 n g ta A gt s kp vp key val (StorageWritePost e h key val evictedRegister st)
          (StorageRead.foundU64 (h.storage key))) := by
  have hne : ∀ w : UInt32, UInt64.ofNat w.toNat ≠ u64Max := by
    intro w h'
    have := w.toNat_lt
    have h'' := congrArg UInt64.toNat h'
    simp [u64Max] at h''
    omega
  have hc := storageWrite_readContract (C := Cg) e h (UInt64.ofNat kl.toNat) (UInt64.ofNat kp.toNat)
    (UInt64.ofNat vl.toNat) (UInt64.ofNat vp.toNat) evictedRegister key val st (hne kl) (hne vl)
    (by rw [toNat_ofNat32]; exact hkl) (by rw [toNat_ofNat32]; exact hvl) (by rw [toNat_ofNat32]; exact hkpos)
    (by rw [toNat_ofNat32]; exact hvpos) hview hacc hlim hvlim hb hz hlink hproof hbud (fun v hv _ => hreg v hv)
  rw [toNat_ofNat32, toNat_ofNat32, toNat_ofNat32, toNat_ofNat32, StorageRead.storageReadResult_eq] at hc
  have hv : StorageRead.foundU64 (h.storage key) = 0 ∨ StorageRead.foundU64 (h.storage key) = 1 := by
    unfold StorageRead.foundU64; split <;> simp
  exact f547_spec cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s kp kl vp vl hs hal key val h _ _ hv _
    hdj hc

end Spec

end WNear.Binary.StorageWrite
