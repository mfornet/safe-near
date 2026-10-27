import Bridge.Functions.ValueReturn
import NearLogic.CallPred
import NearLogic.Hosts.StorageRead

/-!
# `storage_read` through the blockchain interface (459 and 284)

`env::storage_read(key)` (548) calls

```wat
;; 459 LocalKey::with(key, &slice) -> u64: as 440 (RegisterLen.lean), the
;; vtable slot 188 (index 82), the arguments (data, len, ptr, 0) as u64
;; (register 0); then Result::expect (432) on Ok

;; 284: local.get 1  local.get 2  local.get 3  call 43   ;; the storage_read host
```

* `f284_spec`: the trampoline: 4 instructions and the host's `kh`, for any
  `ReadContractP` of the host (`storageRead_readContract` gives one, with
  `kh = storageReadUse h key len` and the post `StorageReadPost h key r s`).
* `f459_spec`: `LocalKey::with` on the installed interface: 249
  `regular_op_cost`s and the host's gas; the host's result (`v`, 1 found / 0
  not) returned.

548 itself (the `read_register` of the value, 523, and its `Option` on the
shadow stack) is not covered here.
-/

namespace WNear.Binary.StorageRead

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-- What `storage_read` returns, as a `u64`: 1 found, 0 not. -/
def foundU64 (val : Option (List UInt8)) : UInt64 :=
  match val with
  | some _ => 1
  | none => 0

theorem storageReadResult_eq (val : Option (List UInt8)) :
    storageReadResult val = [.i64 (foundU64 val)] := by
  cases val <;> rfl

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}
  {Cg K : Nat}

/-- `mwpi_call_host_ro_pred` on a stack holding just the arguments, the
credits any `K` covering the call and the host's gas. -/
theorem mwpi_call_host_ro_pred' (i a n ptr : Nat) (fn : HostFn NearState) (h : NearState)
    (Q : NearState → Prop) (mx : Option Nat) (bs : List UInt8) (args rs : List Value) {kh : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length)
    (hc : ReadContractP fn h Q args rs ptr bs kh Cg) :
    credits Cg K ∗ ⌜cfg.regularOpCost + kh ≤ K⌝ ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗
      mhostPt h ∗ n ↦[wms][ ptr ] bs ∗
      ▷ (∀ h', ⌜Q h'⌝ -∗ mhostPt h' -∗ n ↦[wms][ ptr ] bs -∗
        credits Cg (K - (cfg.regularOpCost + kh)) -∗ Φ.normal rs f)
      ⊢ mwpi cfg lim d f args [.call i] Φ := by
  iintro ⟨Hc, %hK, Hf, Hm, Hh, Hb, H⟩
  have r := mwpi_call_host_ro_pred (cfg := cfg) (lim := lim) (d := d) (f := f) (Φ := Φ)
    (R := K - (cfg.regularOpCost + kh)) i a n ptr fn h Q mx bs [] args rs ha hn hlen hc
  simp only [List.nil_append] at r
  iapply r
  rw [show cfg.regularOpCost + kh + (K - (cfg.regularOpCost + kh)) = K by omega]
  iframe Hc Hf Hm Hh Hb H

end Flex

/-! ## The trampoline (284) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (len ptr r : UInt64) (key : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 len, .i64 ptr, .i64 r]⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] key)

def trampPost (n : Nat) (Q : NearState → Prop) (ptr : UInt64) (key : List UInt8) (v : UInt64)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ (∃ h', ⌜Q h'⌝ ∗ mhostPt h') ∗ n ↦[wms][ ptr.toNat ] key)

/-- `VmBlockchainInterface::storage_read` (284, the vtable's index 82):
`storage_read(len, ptr, r)` (import 43) of the key at `ptr`, under any read
contract of the host. -/
theorem f284_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e n a43 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[43]? = some a43)
    (Cg : Nat) (h : NearState) (Q : NearState → Prop) (dp : UInt32) (len ptr r v : UInt64)
    (key : List UInt8) (kh : Nat)
    (hc : ReadContractP (metered e "storage_read" storageReadFn).toHostFn h Q
      [.i64 len, .i64 ptr, .i64 r] [.i64 v] ptr.toNat key kh Cg) :
    a43 ↪[wf] FuncInst.host (metered e "storage_read" storageReadFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f284 Cg (trampPre n h dp len ptr r key)
        (fun _ => 4 * cfg.regularOpCost + kh) (trampPost n Q ptr key v) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hb⟩
  subst hargs
  simp only [f284]
  mstep; mstep; mstep
  iapply mwpi_call_host_ro_pred' 43 a43 n ptr.toNat _ h Q mx key [.i64 len, .i64 ptr, .i64 r]
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

/-! ## `LocalKey::with` (459), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key and a pointer to the key slice `(ptr, len)`; the stack pointer,
the interface, the frame below `sp`, the key's bytes and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (key : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 sl]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] key ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (key : List UInt8) (Q : NearState → Prop) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] key ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.storage_read(key, 0))` (459) on the
installed interface, register 0, under a read contract `hc` of the host
(`storageRead_readContract`): 249 `regular_op_cost`s and the host's `kh`. -/
theorem f459_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (Q : NearState → Prop) (sl ptr len : UInt32)
    (key : List UInt8) (v : UInt64) (kh : Nat)
    (hc : ReadContractP (metered e "storage_read" storageReadFn).toHostFn h Q
      [.i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat), .i64 0] [.i64 v] ptr.toNat key kh Cg)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f459 Cg
        (withPre n g ta A gi sp sl ptr len key w0 w4 w8 w12 h)
        (fun _ => 249 * cfg.regularOpCost + kh)
        (withPost n g ta A gi sp sl ptr len key Q v) := by
  iintro #Hcode
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260,
    #F284, #H1, #H20, #H43, #Hm, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, Sp, Sl, HF, Hb, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, ⟨S188, T82⟩⟩
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
  simp only [f459]
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
      (sp - 16) 1074904 1056340 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mstep; mstep
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056356
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `storage_read`
  mstep; mstep [Hda]; mstep; mstep [Sl]; mstep; mstep [Sp]
  simp only [load32u, UInt32.reduceOfNat]
  mstep
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S188]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 6) (t := 0) (ta := ta) (idx := 82) (a := A 284)
    (type := types[6]!) (inst := inst) (mi := mi) (code := f284)
    [.i32 1, .i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat), .i64 0])
  isplitr
  · iapply (f284_spec cfg lim (d + 1) types[6]! (by rfl) inst mi e n (A 43) mx hm.mem
      (hm.funcs 43 (by decide)) Cg h Q 1 (UInt64.ofNat len.toNat) (UInt64.ofNat ptr.toNat) 0 v key kh
      (by rw [toNat_ofNat32]; exact hc))
    mpersist
  isplitr
  · iexact F284
  isplitr
  · iexact Hi
  isplitl [T82]
  · simp only [UInt32.reduceToNat]; iexact T82
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
  iintro %rs T82 Hc HQ
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
  mstep
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
  iunfold withPost, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 T82 Sp Sl W0 W4 W8 W12 Hb Hhost
  ipureintro; simp [htype]

end With

end WNear.Binary.StorageRead
