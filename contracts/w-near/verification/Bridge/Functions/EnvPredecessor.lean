import Bridge.Functions.EnvDeposit

/-!
# `predecessor_account_id` through the blockchain interface (455 and 245)

`env::predecessor_account_id()` (526) calls

```wat
;; 455 LocalKey::with(key): as 444 (EnvDeposit.lean), the vtable slot 32 (table index 43), the
;; arguments (data, 0) (register 0); Result::expect (433) on Ok
;; 245: local.get 1  call 5           ;; the predecessor_account_id host
```

then `read_register(0)` (523, ReadRegister.lean), `Option::expect` (498) and
`String::from_utf8(..).expect(..)` (512, 499), which are not covered here.

The installed interface (`Interface.iface`) does not hold the vtable slot of
`predecessor_account_id`; `pslot` is it (`slot n ta 32 43 (A 245)`), and `pCode` holds the
trampoline 245 and the host import 5.

* `f245_spec`: the trampoline: `predecessor_account_id(r)` under
  `predecessorAccountId_readContract`, 2 `regular_op_cost`s and `predecessorUse h`.
* `f455_spec`: `LocalKey::with` on the installed interface: register 0 holds the predecessor
  (`predecessorHost h 0`).
-/

namespace WNear.Binary.EnvPredecessor

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-! ## The binary's facts -/

/-- `predecessor_account_id`: the vtable's offset 32 holds the table index 43. -/
theorem vtable_predecessor : dataWord (1050188 + 32) = bytes32 43 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 43: the trampoline 245. -/
theorem wTable_43 : wTable.elems[43]? = some (Ref.func 245) := rfl

/-- Import 5: `predecessor_account_id`. -/
theorem wStore_predecessor (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[5]? =
      some (FuncInst.host
        (metered cfg.fees.numExtraBytesRecord "predecessor_account_id" predecessorAccountIdFn).toHostFn) := by
  simp [wStore, wHosts]

/-! ## The slot and the code -/

section Inv

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The vtable slot of `predecessor_account_id`. -/
def pslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 32 43 (A 245)

/-- The code of `predecessor_account_id` past `ifaceCode`: the trampoline 245 and the host 5. -/
def pCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 245 ↪[wf] FuncInst.wasm types[5]! inst f245 ∗
    A 5 ↪[wf] FuncInst.host (metered e "predecessor_account_id" predecessorAccountIdFn).toHostFn)

instance (e inst : Nat) (A : Nat → Nat) : Persistent (pCode (GF := GF) e inst A) := by
  unfold pCode; infer_instance

theorem pslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 32 ] dataWord (1050188 + 32) ∗ ta ↦[wt][ 43 ] Ref.func (A 245) ⊢
      pslot (GF := GF) n ta A := by
  rw [vtable_predecessor]
  iintro ⟨H, T⟩
  iunfold pslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

end Inv

/-! ## The trampoline (245) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (h : NearState) (dp : UInt32) (r : UInt64) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 r]⌝ ∗ mhostPt h)

def trampPost (h : NearState) (r : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ mhostPt (predecessorHost h r))

/-- `VmBlockchainInterface::predecessor_account_id` (245, the vtable's index 43):
`predecessor_account_id(r)` (import 5), outside a view call, the predecessor a valid account id
within the register limit. -/
theorem f245_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e n a5 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[5]? = some a5)
    (Cg : Nat) (h : NearState) (dp : UInt32) (r : UInt64) (hview : h.context.isView = false)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlim : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true) :
    a5 ↪[wf] FuncInst.host (metered e "predecessor_account_id" predecessorAccountIdFn).toHostFn ∗
      n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f245 Cg (trampPre h dp r)
        (fun _ => 2 * cfg.regularOpCost + predecessorUse h) (trampPost h r) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost⟩
  subst hargs
  simp only [f245]
  mstep
  have hc := predecessorAccountId_readContract (C := Cg) e h r 0 hview hvalid hlim
  iapply mwpi_call_host_ro' 5 a5 n 0 _ h (predecessorHost h r) mx [] [.i64 r] [] ha hn rfl hc
  iframe Hc Hh Hm Hhost
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitr
  · iapply memBytes_nil
  inext
  iintro Hhost - Hc
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold trampPost
  iframe Hhost
  ipureintro; rfl

end Tramp

/-! ## `LocalKey::with` (455), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key; the stack pointer, the interface, the frame below `sp` and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp : UInt32)
    (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ pslot n ta A ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp : UInt32)
    (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ pslot n ta A ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ mhostPt (predecessorHost h 0))

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.predecessor_account_id(0))` (455) on the installed
interface, outside a view call: register 0 holds the predecessor; 232 `regular_op_cost`s and the
host's gas. -/
theorem f455_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (hview : h.context.isView = false)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlim : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx ∗ pCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f455 Cg
        (withPre n g ta A gi sp w0 w4 w8 w12 h)
        (fun _ => 232 * cfg.regularOpCost + predecessorUse h)
        (withPost n g ta A gi sp h) := by
  iintro ⟨#Hcode, #HP⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold pCode at HP
  icases HP with ⟨#F245, #H5⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HPs, HF, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, S188⟩
  iunfold pslot, slot at HPs
  icases HPs with ⟨S32, T43⟩
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
  have ha433 := hm.funcs 433 (by decide)
  have t429 : types[31]!.params.length = 3 := by rfl
  have t430 : types[13]!.params.length = 2 := by rfl
  have t431 : types[0]!.params.length = 1 := by rfl
  have t433 : types[0]!.params.length = 1 := by rfl
  simp only [f455]
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
      (sp - 16) 1074904 1055356 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1055356
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `predecessor_account_id`
  mstep; mstep [Hda]; mstep
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S32]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 5) (t := 0) (ta := ta) (idx := 43) (a := A 245)
    (type := types[5]!) (inst := inst) (mi := mi) (code := f245) [.i32 1, .i64 0])
  isplitr
  · iapply (f245_spec cfg lim (d + 1) types[5]! (by rfl) inst mi e n (A 5) mx hm.mem
      (hm.funcs 5 (by decide)) Cg h 1 0 hview hvalid hlim)
    mpersist
  isplitr
  · iexact F245
  isplitr
  · iexact Hi
  isplitl [T43]
  · simp only [UInt32.reduceToNat]; iexact T43
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hhost]
  · iunfold trampPre
    iframe Hhost
    ipureintro; rfl
  inext
  iintro %rs T43 Hc HQ
  iunfold trampPost at HQ
  icases HQ with ⟨%hrs, Hhost⟩
  subst hrs
  mctrl_norm
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
  mstep
  mcall (BorrowMut.f433_spec cfg lim (d + 1) types[0]! (by rfl) inst mi g hm.glob Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl) using [Hg]
  · iunfold BorrowMut.expectPre
    iframe Hg
    ipureintro; rfl
  iunfold BorrowMut.expectPost at HQ
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  -- sp += 16
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  mcredits R
  iframe Hc
  iunfold withPost, iface, pslot, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 S32 T43 W0 W4 W8 W12 Hhost

end With

end WNear.Binary.EnvPredecessor
