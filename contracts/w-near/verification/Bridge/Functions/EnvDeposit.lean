import Bridge.Functions.ReadRegister
import Bridge.Functions.FtTotalSupplyGetter
import NearLogic.Hosts.Context

/-!
# `env::attached_deposit` (function 529), through the blockchain interface

```wat
;; 529 attached_deposit(out) -> u128 at out
sp -= 16;  [sp] := 0 (i64);  [sp+8] := 0 (i64)
444(1055020, sp)                     ;; BLOCKCHAIN_INTERFACE.with(|b| b.attached_deposit(sp))
out := [sp] (i64);  out+8 := [sp+8] (i64)
sp += 16

;; 444 LocalKey::with(key, p): as 435 (ReadRegister.lean), the vtable slot 64 (table index
;; 51), the arguments (data, p as u64); Result::expect (433) on Ok
;; 253: local.get 1  call 13          ;; the attached_deposit host
```

The installed interface (`Interface.iface`) does not hold the vtable slot of
`attached_deposit`; `dslot` is it (`slot n ta 64 51 (A 253)`), and `dCode` holds the trampoline
253 and the host import 13.

* `f253_spec`: the trampoline: `attached_deposit(ptr)` under `attachedDeposit_rwContract`, 2
  `regular_op_cost`s and `attachedDepositUse h`.
* `f444_spec`: `LocalKey::with` on the installed interface: 233 and the host's gas.
* `f529_spec`: `env::attached_deposit()`: the 16 bytes `leU128Bytes` of the deposit at `out`.
-/

namespace WNear.Binary.EnvDeposit

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.ReadRegister (mwpi_call_host_rw')

/-! ## The binary's facts -/

/-- `attached_deposit`: the vtable's offset 64 holds the table index 51. -/
theorem vtable_attachedDeposit : dataWord (1050188 + 64) = bytes32 51 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 51: the trampoline 253. -/
theorem wTable_51 : wTable.elems[51]? = some (Ref.func 253) := rfl

/-- Import 13: `attached_deposit`. -/
theorem wStore_attachedDeposit (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[13]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "attached_deposit" attachedDepositFn).toHostFn) := by
  simp [wStore, wHosts]

/-! ## The slot and the code -/

section Inv

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The vtable slot of `attached_deposit`. -/
def dslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 64 51 (A 253)

/-- The code of `attached_deposit` past `ifaceCode`: the trampoline 253 and the host 13. -/
def dCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 253 ↪[wf] FuncInst.wasm types[5]! inst f253 ∗
    A 13 ↪[wf] FuncInst.host (metered e "attached_deposit" attachedDepositFn).toHostFn)

instance (e inst : Nat) (A : Nat → Nat) : Persistent (dCode (GF := GF) e inst A) := by
  unfold dCode; infer_instance

theorem dslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 64 ] dataWord (1050188 + 64) ∗ ta ↦[wt][ 51 ] Ref.func (A 253) ⊢
      dslot (GF := GF) n ta A := by
  rw [vtable_attachedDeposit]
  iintro ⟨H, T⟩
  iunfold dslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

end Inv

/-! ## The trampoline (253) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (ptr : UInt64) (old : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 ptr]⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] old)

def trampPost (n : Nat) (h : NearState) (ptr : UInt64) (data : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] data)

/-- `VmBlockchainInterface::attached_deposit` (253, the vtable's index 51):
`attached_deposit(ptr)` (import 13), outside a view call, the deposit written over the 16 `old`
bytes. -/
theorem f253_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e n a13 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[13]? = some a13)
    (Cg : Nat) (h : NearState) (dp : UInt32) (ptr : UInt64) (old : List UInt8)
    (hview : h.context.isView = false) (hold : old.length = 16) :
    a13 ↪[wf] FuncInst.host (metered e "attached_deposit" attachedDepositFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f253 Cg (trampPre n h dp ptr old)
        (fun _ => 2 * cfg.regularOpCost + attachedDepositUse h)
        (trampPost n h ptr (leU128Bytes h.context.attachedDeposit)) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hb⟩
  subst hargs
  simp only [f253]
  mstep
  iapply mwpi_call_host_rw' 13 a13 n ptr.toNat _ h h mx old (leU128Bytes h.context.attachedDeposit)
    [.i64 ptr] [] ha hn rfl (by rw [leU128Bytes_length, hold])
    (attachedDeposit_rwContract (C := Cg) e h ptr old hview hold)
  iframe Hc Hh Hm Hhost Hb
  isplitr
  · ipureintro; mstep_norm_full; omega
  inext
  iintro Hhost Hb Hc
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold trampPost
  iframe Hhost Hb
  ipureintro; rfl

end Tramp

/-! ## `LocalKey::with` (444), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key and the pointer `p` of the deposit's 16 bytes; the stack pointer, the interface, the
frame below `sp`, the bytes and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp p : UInt32) (old : List UInt8)
    (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 p]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ dslot n ta A ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ p.toNat ] old ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp p : UInt32) (data : List UInt8)
    (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ dslot n ta A ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ p.toNat ] data ∗ mhostPt h)

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.attached_deposit(p))` (444) on the installed interface,
outside a view call: 233 `regular_op_cost`s and the host's gas. -/
theorem f444_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (p : UInt32) (old : List UInt8)
    (hview : h.context.isView = false) (hold : old.length = 16)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx ∗ dCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f444 Cg
        (withPre n g ta A gi sp p old w0 w4 w8 w12 h)
        (fun _ => 233 * cfg.regularOpCost + attachedDepositUse h)
        (withPost n g ta A gi sp p (leU128Bytes h.context.attachedDeposit) h) := by
  iintro ⟨#Hcode, #HD⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold dCode at HD
  icases HD with ⟨#F253, #H13⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HD, HF, Hb, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, S188⟩
  iunfold dslot, slot at HD
  icases HD with ⟨S64, T51⟩
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
  simp only [f444]
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
      (sp - 16) 1074904 1055436 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1055452
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `attached_deposit`
  mstep; mstep [Hda]; mstep; mstep
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S64]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 5) (t := 0) (ta := ta) (idx := 51) (a := A 253)
    (type := types[5]!) (inst := inst) (mi := mi) (code := f253)
    [.i32 1, .i64 p.toUInt64])
  isplitr
  · iapply (f253_spec cfg lim (d + 1) types[5]! (by rfl) inst mi e n (A 13) mx hm.mem
      (hm.funcs 13 (by decide)) Cg h 1 p.toUInt64 old hview hold)
    mpersist
  isplitr
  · iexact F253
  isplitr
  · iexact Hi
  isplitl [T51]
  · simp only [UInt32.reduceToNat]; iexact T51
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hhost Hb]
  · iunfold trampPre
    try simp only [UInt32.toNat_toUInt64]
    iframe Hhost Hb
  inext
  iintro %rs T51 Hc HQ
  iunfold trampPost at HQ
  icases HQ with ⟨%hrs, Hhost, Hb⟩
  subst hrs
  try simp only [UInt32.toNat_toUInt64]
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
  try simp only [UInt32.toNat_toUInt64]
  mcredits R
  iframe Hc
  iunfold withPost, iface, dslot, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 S64 T51 W0 W4 W8 W12 Hb Hhost

end With

/-! ## `env::attached_deposit` (529) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.ReadRegister (stk_frame4 frame4_stk)
open WNear.Binary.U128From (memBytes_split memBytes_join)
open WNear.Binary.FtTotalSupplyGetter (storeBytes_load_i64 toNat_add8)

def pre529 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (ob : List UInt8)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ dslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post529 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (h : NearState)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ iface n ta A ∗ dslot n ta A ∗
    stk n (s.toNat - 32) 32 ∗ n ↦[wms][ out.toNat ] leU128Bytes h.context.attachedDeposit ∗ mhostPt h)

theorem storeBytes_i64_0_length : (storeBytes (.i64 0) 8).length = 8 := by simp [storeBytes]

set_option maxHeartbeats 4000000 in
/-- **`env::attached_deposit()`** (function 529 of `contract.wasm`) on the installed interface,
outside a view call: the deposit's 16 little-endian bytes at `out`, the host unchanged up to gas;
41 `regular_op_cost`s more than 444. -/
theorem f529_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 32 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (ob : List UInt8) (hob : ob.length = 16) (h : NearState)
    (hview : h.context.isView = false) :
    ifaceCode e inst mi A n mx ∗ dCode e inst A ∗ A 444 ↪[wf] FuncInst.wasm types[14]! inst f444
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f529 Cg (pre529 n g ta A gt s out ob h)
        (fun _ => 41 * cfg.regularOpCost + (233 * cfg.regularOpCost + attachedDepositUse h))
        (post529 n g ta A gt s out h) := by
  iintro ⟨#Hcode, #HD, #F444⟩
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = (s - 16).toNat + 8 := by simp [UInt32.toNat_add, h16]; omega
  have e32 : (s - 16 - 16).toNat = s.toNat - 32 := by
    have h1 : (16 : UInt32) ≤ s - 16 := by rw [UInt32.le_iff_toNat_le, h16]; simp; omega
    rw [UInt32.toNat_sub_of_le _ _ h1, h16]; simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre529 at HP
  icases HP with ⟨%hargs, Hg, HI, HDs, Hs, Ho, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Fr, Hs⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Hs with ⟨D1, D2⟩
  iunfold stk at D1 D2
  icases D1 with ⟨%b1, %hb1, D1⟩
  icases D2 with ⟨%b2, %hb2, D2⟩
  icases stk_frame4 n (s.toNat - 32) (s - 16 - 16) e32 $$ Fr with ⟨%w0, %w4, %w8, %w12, Fr⟩
  ihave D1 := memBytes_addr (show s.toNat - 32 + 16 = (s - 16).toNat by omega) $$ D1
  ihave D2 := memBytes_addr (show s.toNat - 32 + 16 + 8 = (s - 16 + 8).toNat by omega) $$ D2
  have hn := hm.mem
  have hg := hm.glob
  have ha444 := hm.funcs 444 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  simp only [f529]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep [D2]
  mstep; mstep; mstep [D1]
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hs16 : 16 ≤ (s - 16).toNat := by omega
  have hal16 : (s - 16).toNat % 8 = 0 := by omega
  ihave D2 := memBytes_addr (b := (s - 16).toNat + 8) (by omega) $$ D2
  ihave D := memBytes_join n (s - 16).toNat 8 (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8)
    storeBytes_i64_0_length $$ [D1 D2]
  · isplitl [D1] <;> iassumption
  mstep; mstep
  mcall (f444_spec cfg lim (d + 1) types[14]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 16)⟩ (s - 16) rfl hs16 hal16 h (s - 16)
      (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) hview (by simp [storeBytes]) w0 w4 w8 w12)
    using [Hg HI HDs Fr D Hhost]
  · iunfold withPre
    iframe Hg HI HDs Fr D Hhost
    ipureintro; rfl
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, HDs, Fr, D, Hhost⟩
  subst hrs
  have hl16 := leU128Bytes_length h.context.attachedDeposit
  icases memBytes_split n (s - 16).toNat 8 (leU128Bytes h.context.attachedDeposit) (by omega) $$ D
    with ⟨D1, D2⟩
  ihave D2 := memBytes_addr (b := (s - 16 + 8).toNat) (by omega) $$ D2
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨Ho1, Ho2⟩
  mstep; mstep [D1]; mstep
  mstep; mstep; mstep [D2]; mstep [Ho2]
  mstep; mstep
  mstep [Ho1]
  -- sp += 16
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  have l1 := storeBytes_load_i64 ((leU128Bytes h.context.attachedDeposit).take 8) (by simp; omega)
  have l2 := storeBytes_load_i64 ((leU128Bytes h.context.attachedDeposit).drop 8) (by simp; omega)
  simp only [loadValue] at l1 l2
  rw [l1, l2]
  mcredits R
  iframe Hc
  iunfold post529
  isplitr
  · ipureintro; rfl
  iframe Hg HI HDs Hhost
  isplitl [Fr D1 D2]
  · ihave Fr := frame4_stk n (s.toNat - 32) _ e32 _ _ _ _ $$ Fr
    ihave D2 := memBytes_addr (b := (s - 16).toNat + 8) (by omega) $$ D2
    ihave D := memBytes_join n (s - 16).toNat 8 ((leU128Bytes h.context.attachedDeposit).take 8)
      ((leU128Bytes h.context.attachedDeposit).drop 8) (by simp [hl16]) $$ [D1 D2]
    · isplitl [D1] <;> iassumption
    rw [List.take_append_drop]
    ihave D := stk_intro n _ _ $$ D
    rw [hl16]
    ihave D := stk_addr (show (s - 16).toNat = s.toNat - 32 + 16 by omega) $$ D
    iapply stk_join n (s.toNat - 32) 16 16
    iframe Fr D
  ihave Ho := memBytes_join n out.toNat 8 ((leU128Bytes h.context.attachedDeposit).take 8)
    ((leU128Bytes h.context.attachedDeposit).drop 8) (by simp [hl16]) $$ [Ho1 Ho2]
  · isplitl [Ho1] <;> iassumption
  rw [List.take_append_drop]
  iexact Ho

end Spec

end WNear.Binary.EnvDeposit
