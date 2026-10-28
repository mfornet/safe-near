import Bridge.Functions.ReadRegister
import NearLogic.Hosts.EnvGetters

/-!
# `env::storage_usage` (528) and `env::attached_deposit` (529), through the blockchain interface

```wat
;; 528 storage_usage() -> u64
call 460(1055020)

;; 460 LocalKey::with(key) -> u64: as 440 (RegisterLen.lean) without the argument, the
;; vtable slot 52 (index 48), `call_indirect (type 11)` on (data)
;; 250: call 10                                 ;; the storage_usage host

;; 529 attached_deposit(out): u128 at out
sp -= 16;  [sp+8] := 0;  [sp] := 0 (i64)
call 444(1055020, sp)                           ;; BLOCKCHAIN_INTERFACE.with(|b| b.attached_deposit(sp))
[out+8] := [sp+8];  [out] := [sp]
sp += 16

;; 444 LocalKey::with(key, ptr): as 456 (ValueReturn.lean), the vtable slot 64 (index 51),
;; `call_indirect (type 5)` on (data, ptr as u64); then `Result::expect` (433) on Ok
;; 253: local.get 1  call 13                    ;; the attached_deposit host
```

The two vtable slots are not in `Interface.iface`: `uslot` (offset 52, index 48, the trampoline
250) and `dslot` (offset 64, index 51, the trampoline 253) sit beside it, their code in `uCode`
and `dCode` (as `StorageWrite.wslot`/`wCode`).

* `f250_spec`, `f460_spec`, `f528_spec`: under any `ReadContract` of the host returning `v`,
  the host ending as `h'` (up to gas). `f528_spec_host`: with `storageUsage_readContract`,
  `v = h.context.storageUsage`, the host unchanged, the gas `storageUsageUse h`.
* `f253_spec`, `f444_spec`, `f529_spec`: under any `RWContract` of the host writing
  `u128Bytes lo hi` over the zeroed 16 bytes at `sp - 16`. `f529_spec_host`: with
  `attachedDeposit_rwContract` (outside a view call), `out` holds the deposit's two words
  `depLo h`, `depHi h` (`depLo_add_depHi`: `lo + 2^64 hi` is the deposit below `2^128`), the host
  unchanged, the gas `attachedDepositUse h`.
-/

namespace WNear.Binary.EnvGetters

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.U128From (u128Bytes)

/-! ## The binary's facts -/

/-- `storage_usage`: the vtable's offset 52 holds the table index 48. -/
theorem vtable_storageUsage : dataWord (1050188 + 52) = bytes32 48 := by
  rw [dataWord_eq _ (by decide)]; decide

/-- `attached_deposit`: the vtable's offset 64 holds the table index 51. -/
theorem vtable_attachedDeposit : dataWord (1050188 + 64) = bytes32 51 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entries 48 and 51: the trampolines 250 and 253. -/
theorem wTable_envGetters : wTable.elems[48]? = some (Ref.func 250) ∧
    wTable.elems[51]? = some (Ref.func 253) := ⟨rfl, rfl⟩

/-- Imports 10 and 13: `storage_usage` and `attached_deposit`. -/
theorem wStore_envGetters (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[10]? =
        some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "storage_usage" storageUsageFn).toHostFn) ∧
      (wStore cfg h).funcs[13]? =
        some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "attached_deposit"
          attachedDepositFn).toHostFn) := by
  refine ⟨?_, ?_⟩ <;> simp [wStore, wHosts]

/-! ## The vtable slots and their code -/

section Inv

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `storage_usage` slot of the vtable: offset 52, table index 48, the trampoline 250. -/
def uslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 52 48 (A 250)

/-- The `attached_deposit` slot of the vtable: offset 64, table index 51, the trampoline 253. -/
def dslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 64 51 (A 253)

/-- The code of `storage_usage` past `ifaceCode`: the trampoline 250 and the host 10. -/
def uCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 250 ↪[wf] FuncInst.wasm types[11]! inst f250 ∗
    A 10 ↪[wf] FuncInst.host (metered e "storage_usage" storageUsageFn).toHostFn)

/-- The code of `attached_deposit` past `ifaceCode`: the trampoline 253 and the host 13. -/
def dCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 253 ↪[wf] FuncInst.wasm types[5]! inst f253 ∗
    A 13 ↪[wf] FuncInst.host (metered e "attached_deposit" attachedDepositFn).toHostFn)

instance (e inst : Nat) (A : Nat → Nat) : Persistent (uCode (GF := GF) e inst A) := by
  unfold uCode; infer_instance

instance (e inst : Nat) (A : Nat → Nat) : Persistent (dCode (GF := GF) e inst A) := by
  unfold dCode; infer_instance

theorem uslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 52 ] dataWord (1050188 + 52) ∗ ta ↦[wt][ 48 ] Ref.func (A 250) ⊢
      uslot (GF := GF) n ta A := by
  rw [vtable_storageUsage]
  iintro ⟨H, T⟩
  iunfold uslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

theorem dslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 64 ] dataWord (1050188 + 64) ∗ ta ↦[wt][ 51 ] Ref.func (A 253) ⊢
      dslot (GF := GF) n ta A := by
  rw [vtable_attachedDeposit]
  iintro ⟨H, T⟩
  iunfold dslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

end Inv

/-! ## The `storage_usage` trampoline (250) -/

section TrampU

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def uTrampPre (h : NearState) (dp : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp]⌝ ∗ mhostPt h)

def uTrampPost (h' : NearState) (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ mhostPt h')

/-- `VmBlockchainInterface::storage_usage` (250, the vtable's index 48): `storage_usage()`
(import 10), under any read contract of the host returning `v`. -/
theorem f250_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e n a10 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[10]? = some a10)
    (Cg : Nat) (h h' : NearState) (dp : UInt32) (v : UInt64) (kh : Nat)
    (hc : ReadContract (metered e "storage_usage" storageUsageFn).toHostFn h h' [] [.i64 v] 0 [] kh Cg) :
    a10 ↪[wf] FuncInst.host (metered e "storage_usage" storageUsageFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f250 Cg (uTrampPre h dp)
        (fun _ => cfg.regularOpCost + kh) (uTrampPost h' v) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold uTrampPre at HP
  icases HP with ⟨%hargs, Hhost⟩
  subst hargs
  simp only [f250]
  iapply mwpi_call_host_ro' 10 a10 n 0 _ h h' mx [] [] [.i64 v] ha hn rfl hc
  iframe Hc Hh Hm Hhost
  isplitr
  · ipureintro; omega
  isplitr
  · iapply memBytes_nil
  inext
  iintro Hhost - Hc
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold uTrampPost
  iframe Hhost
  ipureintro; simp [htype]

end TrampU

/-! ## `LocalKey::with` (460), the interface installed -/

section WithU

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key; the stack pointer, the interface and its `storage_usage` slot, the frame below `sp`,
the host. -/
def withPreU (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp : UInt32) (w0 w4 w8 w12 : UInt32)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ uslot n ta A ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ mhostPt h)

def withPostU (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp : UInt32) (h' : NearState)
    (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ uslot n ta A ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ mhostPt h')

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.storage_usage())` (460) on the installed interface, under a
read contract `hc` of the host: 240 `regular_op_cost`s and the host's `kh`. -/
theorem f460_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h h' : NearState) (v : UInt64) (kh : Nat)
    (hc : ReadContract (metered e "storage_usage" storageUsageFn).toHostFn h h' [] [.i64 v] 0 [] kh Cg)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx ∗ uCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f460 Cg
        (withPreU n g ta A gi sp w0 w4 w8 w12 h)
        (fun _ => 240 * cfg.regularOpCost + kh) (withPostU n g ta A gi sp h' v) := by
  iintro ⟨#Hcode, #Hu⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold uCode at Hu
  icases Hu with ⟨#F250, #H10⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPreU at HP
  icases HP with ⟨%hargs, Hg, HI, HU, HF, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, S188⟩
  iunfold uslot, slot at HU
  icases HU with ⟨S52, T48⟩
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
  have ha429 := hm.funcs 429 (by decide)
  have ha430 := hm.funcs 430 (by decide)
  have ha431 := hm.funcs 431 (by decide)
  have ha432 := hm.funcs 432 (by decide)
  have t429 : types[31]!.params.length = 3 := by rfl
  have t430 : types[13]!.params.length = 2 := by rfl
  have t431 : types[0]!.params.length = 1 := by rfl
  have t432 : types[24]!.params.length = 2 := by rfl
  have hg := hm.glob
  have hn := hm.mem
  simp only [f460]
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
      (sp - 16) 1074904 1055404 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1055420
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `storage_usage`
  mstep; mstep [Hda]; mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S52]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 11) (t := 0) (ta := ta) (idx := 48) (a := A 250)
    (type := types[11]!) (inst := inst) (mi := mi) (code := f250) [.i32 1])
  isplitr
  · iapply (f250_spec cfg lim (d + 1) types[11]! (by rfl) inst mi e n (A 10) mx hm.mem
      (hm.funcs 10 (by decide)) Cg h h' 1 v kh hc)
    mpersist
  isplitr
  · iexact F250
  isplitr
  · iexact Hi
  isplitl [T48]
  · simp only [UInt32.reduceToNat]; iexact T48
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hhost]
  · iunfold uTrampPre
    iframe Hhost
    ipureintro; rfl
  inext
  iintro %rs T48 Hc HQ
  iunfold uTrampPost at HQ
  icases HQ with ⟨%hrs, Hhost⟩
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
  mcredits R
  iframe Hc
  ihave HU : uslot (GF := GF) n ta A $$ [S52 T48]
  · iunfold uslot, slot
    simp only [UInt32.reduceToNat, Nat.reduceAdd]
    isplitl [S52]
    · iexact S52
    · iexact T48
  iunfold withPostU, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe HU Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 W0 W4 W8 W12 Hhost
  ipureintro; simp [htype]

end WithU

/-! ## `env::storage_usage` (528) -/

section SpecU

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk)
open WNear.Binary.ReadRegister (stk_frame4 frame4_stk)

/-- No arguments; the stack pointer `s`, the interface and its `storage_usage` slot, the 16 bytes
of `LocalKey::with`'s frame below `s`, the host. -/
def pre528 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s : UInt32) (h : NearState)
    (args : List Value) : IProp GF :=
  iprop(⌜args = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ uslot n ta A ∗
    stk n (s.toNat - 16) 16 ∗ mhostPt h)

/-- The result `v`; the host `h'`. -/
def post528 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s : UInt32) (h' : NearState)
    (v : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 v]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ uslot n ta A ∗
    stk n (s.toNat - 16) 16 ∗ mhostPt h')

/-- **`env::storage_usage()`** (function 528 of `contract.wasm`) on the installed interface,
under a read contract `hc` of the host returning `v` and ending as `h'`: 253 `regular_op_cost`s
and the host's `kh`. -/
theorem f528_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s : UInt32) (hs : 16 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (h h' : NearState) (v : UInt64) (kh : Nat)
    (hc : ReadContract (metered e "storage_usage" storageUsageFn).toHostFn h h' [] [.i64 v] 0 [] kh Cg) :
    ifaceCode e inst mi A n mx ∗ uCode e inst A ∗ A 460 ↪[wf] FuncInst.wasm types[11]! inst f460
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f528 Cg (pre528 n g ta A gt s h)
        (fun _ => 253 * cfg.regularOpCost + kh) (post528 n g ta A gt s h' v) := by
  iintro ⟨#Hcode, #Hu, #F460⟩
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #HCU : (ifaceCode (GF := GF) e inst mi A n mx ∗ uCode e inst A) $$ []
  · isplitr
    · iexact Hcode
    · iexact Hu
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre528 at HP
  icases HP with ⟨%hargs, Hg, HI, HU, Hs, Hhost⟩
  subst hargs
  icases stk_frame4 n (s.toNat - 16) (s - 16) h16 $$ Hs with ⟨%w0, %w4, %w8, %w12, Fr⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha460 := hm.funcs 460 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  simp only [f528]
  mstep
  mcall (f460_spec cfg lim (d + 1) types[11]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 s⟩ s rfl hs hal h h' v kh hc w0 w4 w8 w12) using [Hg HI HU Fr Hhost]
  · iunfold withPreU
    iframe Hg HI HU Fr Hhost
    ipureintro; rfl
  iunfold withPostU at HQ
  icases HQ with ⟨%hrs, Hg, HI, HU, Fr, Hhost⟩
  subst hrs
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold post528
  ihave Fr := frame4_stk n (s.toNat - 16) _ h16 _ _ _ _ $$ Fr
  iframe Hg HI HU Fr Hhost
  ipureintro; simp [htype]

/-- `f528_spec` with the host's `storageUsage_readContract`: the result is the account's storage
usage `h.context.storageUsage`, the host unchanged (gas aside), the gas `storageUsageUse h`. -/
theorem f528_spec_host (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s : UInt32) (hs : 16 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (h : NearState) :
    ifaceCode e inst mi A n mx ∗ uCode e inst A ∗ A 460 ↪[wf] FuncInst.wasm types[11]! inst f460
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f528 Cg (pre528 n g ta A gt s h)
        (fun _ => 253 * cfg.regularOpCost + storageUsageUse h)
        (post528 n g ta A gt s h h.context.storageUsage) :=
  f528_spec cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt s hs hal h h _ _
    (storageUsage_readContract (C := Cg) e h 0)

end SpecU

end WNear.Binary.EnvGetters
