import Bridge.Functions.ReadRegister

/-!
# `env::input` (function 527), through the blockchain interface

```wat
;; 527 input(out) -> Option<Vec<u8>> at out
call 458(1055020)                             ;; BLOCKCHAIN_INTERFACE.with(|b| b.input(0))
call 523(out, 0)                              ;; read_register(0)

;; 458 LocalKey::with(key): as 435 (ReadRegister.lean), the vtable slot 36
;; (table index 44), the arguments (data, 0 as u64)
;; 246: local.get 1  call 6                   ;; the input host
```

`ifaceI` is `ReadRegister.ifaceR` with the vtable slot of `input`
(`slot n ta 36 44 (A 246)`), and `ifaceCodeI` adds the trampoline 246 and the host
import 6 to `ifaceCodeR`. `ifaceI_of_ifaceR` builds `ifaceI` from the vtable word (data
segment) and the table entry; `wTable_44`, `wStore_input` are the binary's facts.

* `f246_spec`: the trampoline: `input(r)` under `input_readContract` (the input within the
  register limit), 2 `regular_op_cost`s and `inputUse h`.
* `f458_spec`: `LocalKey::with` on the installed interface: 232 `regular_op_cost`s and the
  host's gas; the host ends as `inputHost h 0` (register 0 holds the input).
* `f527_spec`: `env::input()`: 25 `regular_op_cost`s, 458's and 523's (`cost527`); `Some(vec)` with `vec` the call's input in a fresh heap
  block (`optVecAt`), for a nonempty input (the `read_register` contract, `RegOk`, needs
  it; an empty input is the parser's reject path).
-/

namespace WNear.Binary.EnvInput

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ReadRegister
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-! ## The binary's facts -/

/-- `input`: the vtable's offset 36 holds the table index 44. -/
theorem vtable_input : dataWord (1050188 + 36) = bytes32 44 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 44: the trampoline 246. -/
theorem wTable_44 : wTable.elems[44]? = some (Ref.func 246) := rfl

/-- Import 6: `input`. -/
theorem wStore_input (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[6]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn) := by
  simp [wStore, wHosts]

/-- `input` into a register other than the sentinel sets it. -/
theorem inputHost_zero (h : NearState) : inputHost h 0 = h.setRegister 0 h.context.input := by
  unfold inputHost; rw [if_neg (by decide)]; rfl

/-! ## The interface with `input` -/

section Inv

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The installed interface with the slots of `read_register` and `input`. -/
def ifaceI (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(ifaceR n ta A ∗ slot n ta 36 44 (A 246))

/-- `ifaceCodeR` and the code of `input`: the trampoline 246 and the host 6. -/
def ifaceCodeI (e : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    IProp GF :=
  iprop(ifaceCodeR e inst mi A n mx ∗ A 246 ↪[wf] FuncInst.wasm types[5]! inst f246 ∗
    A 6 ↪[wf] FuncInst.host (metered e "input" inputFn).toHostFn)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (ifaceCodeI (GF := GF) e inst mi A n mx) := by
  unfold ifaceCodeI; infer_instance

theorem ifaceI_of_ifaceR (n ta : Nat) (A : Nat → Nat) :
    ifaceR n ta A ∗ n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ ta ↦[wt][ 44 ] Ref.func (A 246)
      ⊢ ifaceI (GF := GF) n ta A := by
  rw [vtable_input]
  iintro ⟨HI, H, T⟩
  iunfold ifaceI, slot
  simp only [UInt32.reduceToNat]
  iframe HI H T

end Inv

/-! ## The trampoline (246) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (h : NearState) (dp : UInt32) (r : UInt64) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 r]⌝ ∗ mhostPt h)

def trampPost (h : NearState) (r : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ mhostPt (inputHost h r))

/-- `VmBlockchainInterface::input` (246, the vtable's index 44): `input(r)` (import 6), the
input within the register limit. -/
theorem f246_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e n a6 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[6]? = some a6)
    (Cg : Nat) (h : NearState) (dp : UInt32) (r : UInt64)
    (hlim : withinLimit h.config.maxRegisterLen h.context.input.length = true) :
    a6 ↪[wf] FuncInst.host (metered e "input" inputFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f246 Cg (trampPre h dp r)
        (fun _ => 2 * cfg.regularOpCost + inputUse h) (trampPost h r) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost⟩
  subst hargs
  simp only [f246]
  mstep
  have hc := input_readContract (C := Cg) e h r 0 hlim
  iapply mwpi_call_host_ro' 6 a6 n 0 _ h (inputHost h r) mx [] [.i64 r] [] ha hn rfl hc
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

/-! ## `LocalKey::with` (458), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp : UInt32)
    (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020]⌝ ∗ g ↦[wg] gi ∗ ifaceI n ta A ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp : UInt32) (h : NearState)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ ifaceI n ta A ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ mhostPt (inputHost h 0))

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.input(0))` (458) on the installed interface: 232
`regular_op_cost`s and the host's gas; register 0 then holds the input. -/
theorem f458_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState)
    (hlim : withinLimit h.config.maxRegisterLen h.context.input.length = true)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCodeI e inst mi A n mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f458 Cg
        (withPre n g ta A gi sp w0 w4 w8 w12 h)
        (fun _ => 232 * cfg.regularOpCost + inputUse h)
        (withPost n g ta A gi sp h) := by
  iintro #HcodeI
  iunfold ifaceCodeI, ifaceCodeR, ifaceCode at HcodeI
  icases HcodeI with ⟨⟨⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩, #F240, #H0⟩, #F246, #H6⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HF, Hhost⟩
  subst hargs
  iunfold ifaceI, ifaceR, iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨⟨⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, S188⟩, ⟨S12, T38⟩⟩, ⟨S36, T44⟩⟩
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
  simp only [f458]
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
      (sp - 16) 1074904 1055388 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1055388
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `input`
  mstep; mstep [Hda]; mstep; mstep
  mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S36]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 5) (t := 0) (ta := ta) (idx := 44) (a := A 246)
    (type := types[5]!) (inst := inst) (mi := mi) (code := f246) [.i32 1, .i64 0])
  isplitr
  · iapply (f246_spec cfg lim (d + 1) types[5]! (by rfl) inst mi e n (A 6) mx hm.mem
      (hm.funcs 6 (by decide)) Cg h 1 0 hlim)
    mpersist
  isplitr
  · iexact F246
  isplitr
  · iexact Hi
  isplitl [T44]
  · simp only [UInt32.reduceToNat]; iexact T44
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
  iintro %rs T44 Hc HQ
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
  try rw [toNat_ofNat32]
  mcredits R
  iframe Hc
  iunfold withPost, ifaceI, ifaceR, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 S12 T38 S36 T44 W0 W4 W8 W12 Hhost

end With

/-! ## `env::input` (527) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.VecFromElem (stk stk_split stk_join)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)

/-- The code `input` runs (persistent): `read_register`'s, the trampoline 246 and the host 6,
458 and 523. -/
def inCode (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(rrCode e inst mi A n maxP mx ∗ A 246 ↪[wf] FuncInst.wasm types[5]! inst f246 ∗
    A 6 ↪[wf] FuncInst.host (metered e "input" inputFn).toHostFn ∗
    A 458 ↪[wf] FuncInst.wasm types[0]! inst f458 ∗ A 523 ↪[wf] FuncInst.wasm types[5]! inst f523)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (inCode (GF := GF) e inst mi A n maxP mx) := by
  unfold inCode; infer_instance

/-- The register after `input(0)` holds the input. -/
theorem inputHost_reg (h : NearState) : (inputHost h 0).registers (0 : UInt64).toNat = some h.context.input := by
  rw [inputHost_zero]; simp [NearState.setRegister]

/-- The cost of `input`. -/
def cost527 (cfg : WasmConfig) (h : NearState) : Nat :=
  25 * cfg.regularOpCost + (232 * cfg.regularOpCost + inputUse h) + cost523 cfg (inputHost h 0) 0

def pre527 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (ob : List UInt8) (h : NearState) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 160) 160 ∗
    vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1 ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post527 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 160) 160 ∗
    vt n 1057464 idx ta (A 578) ∗ optVecAt n maxP len live out (some h.context.input) ∗
    mhostPt (inputHost h 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`env::input()`** (function 527 of `contract.wasm`) on the installed interface (with
the slots of `read_register` and `input`): `Some(vec)` at `out`, `vec` the call's input in a
fresh heap block (`optVecAt`); the host ends with the input in register 0. The input is
nonempty, within the register limit, and fits the heap (`RegOk`). -/
theorem f527_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 160 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (hlim : withinLimit h.config.maxRegisterLen h.context.input.length = true)
    (hok : RegOk maxP len (some h.context.input)) :
    inCode e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f527 Cg
        (pre527 n g ta A gt s out idx maxP len live ob h)
        (fun _ => cost527 cfg h)
        (post527 n g ta A gt s out idx maxP len live h) := by
  iintro #Hin
  iunfold inCode at Hin
  icases Hin with ⟨#Hrr, #F246, #H6, #F458, #F523⟩
  ihave #HcI : ifaceCodeI e inst mi A n mx $$ []
  · iunfold rrCode at Hrr
    icases Hrr with ⟨#HcR, -⟩
    iunfold ifaceCodeI
    iframe HcR F246 H6
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCodeI, ifaceCodeR, ifaceCode at HcI
    icases HcI with ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩, -⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha458 := hm.funcs 458 (by decide)
  have ha523 := hm.funcs 523 (by decide)
  have t0 : types[0]!.params.length = 1 := by rfl
  have t5 : types[5]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre527 at HP
  icases HP with ⟨%hargs, Hg, HI, Hs, Hvt, Hinv, Ho, Hhost⟩
  subst hargs
  icases stk_split n (s.toNat - 160) 144 16 $$ Hs with ⟨Hs, W⟩
  rw [show s.toNat - 160 + 144 = s.toNat - 16 by omega]
  icases stk_frame4 n (s.toNat - 16) (s - 16) h16 $$ W with ⟨%w0, %w4, %w8, %w12, W⟩
  simp only [f527, cost527]
  mstep
  mcall (f458_spec cfg lim (d + 1) types[0]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 s⟩ s rfl (by omega) hal h hlim w0 w4 w8 w12) using [Hg HI W Hhost]
  · iunfold withPre
    iframe Hg HI W Hhost
    ipureintro; rfl
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, W, Hhost⟩
  subst hrs
  ihave W := frame4_stk n (s.toNat - 16) (s - 16) h16 _ _ _ _ $$ W
  ihave Hs := stk_join n (s.toNat - 160) 144 16 $$ [Hs W]
  · rw [show s.toNat - 160 + 144 = s.toNat - 16 by omega]; iframe Hs W
  iunfold ifaceI at HI
  icases HI with ⟨HI, HS36⟩
  mstep; mstep
  have hok' : RegOk maxP len ((inputHost h 0).registers (0 : UInt64).toNat) := by
    rw [inputHost_reg]; exact hok
  mcall (f523_spec cfg lim (d + 1) types[5]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt s out hs
      hal hout 0 idx maxP len live ob hob (inputHost h 0) hok') using [Hg HI Hs Hvt Hinv Ho Hhost]
  · iunfold pre523
    iframe Hg HI Hs Hvt Hinv Ho Hhost
    ipureintro; rfl
  iunfold post523 at HQ
  icases HQ with ⟨%hrs, Hg, HI, Hs, Hvt, Hv, Hhost⟩
  subst hrs
  rw [inputHost_reg]
  mcredits R
  iframe Hc
  iunfold post527, ifaceI
  iframe Hg HI HS36 Hs Hvt Hv Hhost
  ipureintro; simp [htype]

end Spec

end WNear.Binary.EnvInput
