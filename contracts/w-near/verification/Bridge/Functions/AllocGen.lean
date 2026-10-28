import Bridge.Functions.AllocAlloc
import Bridge.Functions.AllocLimit

/-!
# `WeeAlloc::alloc` (581) and `__rust_alloc` (310) for any first walk, the limit held (M4)

`AllocAlloc.f581_fresh` proves 581 on an empty free list. This file proves it once for
*any* first walk: 581's first call to `alloc_first_fit` (580) is given by a specification
`walkSpec` (a persistent hypothesis) whose precondition is the slot `sp - 4` holding the
head `h` plus a resource `PW`, and whose result is either

* `0` with the slot emptied, the policy's vtable slot `vt` and a resource `Z` (the walk
  failed; whatever it left, e.g. a leaked cell, is in `Z`), or
* `r ≠ 0` with the slot holding some `v` and a resource `W r v`.

On `0` 581 grows memory (577, here `AllocLimit.f577_lim`, holding the memory's limit) and
walks the fresh cell (`f580_one`). The result `res581G`:

* `p ≠ 0`, `ALLOC = v`, `W p v`, the memory length unchanged (first walk succeeded);
* `p = 0`, `ALLOC = 0`, `vt ∗ Z`, `¬ GrowOk len (some maxP) P` (the limit forbade the grow);
* the memory grown by `P` pages, `Z`, and 580's `post1` on the fresh cell (as `res581`).

Cost: `910 regular_op_cost`s (630 of `f581_fresh` with the first walk's 21 raised to 300)
plus `memory.grow`'s charge. `f310_gen`: through `AllocWrap`, `15 + 15 + 910` plus the grow.

`MFunSpec_cost` (a larger cost bound is still a bound) and `MFunSpec_exists` (a
precondition's existential) are general helpers.
-/

namespace WNear.Binary.AllocGen

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocLeaves WNear.Binary.AllocFirstFit WNear.Binary.AllocNewCell
open WNear.Binary.AllocAlloc (wordsOf chunkEnd post1_move)
open WNear.Binary.AllocLimit (f577_lim postL)
open WNear.Binary.Interface (IfaceMod)
set_option maxRecDepth 20000

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

instance MFunSpec_persistent {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType}
    {inst : Nat} {mi : ModuleInst} {code : Func} {Cg : Nat} {P : List Value → IProp GF}
    {K : List Value → Nat} {Q : List Value → List Value → IProp GF} :
    Persistent (MFunSpec cfg lim d type inst mi code Cg P K Q) := by
  unfold MFunSpec; infer_instance

/-- A larger cost bound is still a bound. -/
theorem MFunSpec_cost {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P : List Value → IProp GF} {K K' : List Value → Nat}
    {Q : List Value → List Value → IProp GF} (hK : ∀ args, K args ≤ K' args) :
    MFunSpec cfg lim d type inst mi code Cg P K Q ⊢ MFunSpec cfg lim d type inst mi code Cg P K' Q := by
  unfold MFunSpec
  iintro #H
  imodintro
  iintro %args %R HP Hc
  rw [show K' args + R = K args + (R + (K' args - K args)) by have := hK args; omega]
  iapply mwpInvoke_wand
  isplitl [HP Hc]
  · iapply H $$ %args %(R + (K' args - K args)) HP Hc
  isplit
  · dsimp only
    iintro %rs ⟨Hc, HQ⟩
    iframe HQ
    iapply credits_mono (by omega) $$ Hc
  · iintro HT; iexact HT

/-- A precondition's existential, eliminated. -/
theorem MFunSpec_exists {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {α : Type} {P : α → List Value → IProp GF}
    {K : List Value → Nat} {Q : List Value → List Value → IProp GF} :
    (□ ∀ x, MFunSpec cfg lim d type inst mi code Cg (P x) K Q) ⊢
      MFunSpec cfg lim d type inst mi code Cg (fun args => iprop(∃ x, P x args)) K Q := by
  unfold MFunSpec
  iintro #H
  imodintro
  iintro %args %R ⟨%x, HP⟩ Hc
  ispecialize H $$ %x
  icases H with #H
  iapply H $$ %args %R HP Hc

/-- What the first walk leaves (see the module doc). -/
def walkQ (n : Nat) (slot : Nat) (idx : UInt32) (ta a578 : Nat) (Z : IProp GF)
    (W : UInt32 → UInt32 → IProp GF) (_args rs : List Value) : IProp GF :=
  iprop(∃ r : UInt32, ⌜rs = [.i32 r]⌝ ∗
    ((⌜r = 0⌝ ∗ n ↦[i32][ slot ] 0 ∗ vt n 1057464 idx ta a578 ∗ Z) ∨
     (⌜r ≠ 0⌝ ∗ ∃ v : UInt32, n ↦[i32][ slot ] v ∗ W r v)))

/-- The first walk's specification, at 581's slot `sp - 4` holding the head `h`. -/
abbrev walkSpec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (Cg : Nat)
    (n : Nat) (sp size al h idx : UInt32) (ta a578 : Nat) (PW Z : IProp GF)
    (W : UInt32 → UInt32 → IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[34]! inst mi f580 Cg
    (fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
      .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] h ∗ PW))
    (fun _ => 300 * cfg.regularOpCost)
    (walkQ n (UInt32.ofNat (sp.toNat - 4)).toNat idx ta a578 Z W)

/-- 581's precondition: the shadow stack, `ALLOC = h`, the memory length. -/
def pre581G (n g : Nat) (gt : GlobalType) (sp h : UInt32) (len : Nat) (o1 o2 o4 : List UInt8) :
    IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗
    n ↦[wms][ sp.toNat - 4 ] o4 ∗ n ↦[i32][ 1074896 ] h ∗ n ↦[wmlength] len)

/-- What 581 leaves (see the module doc). -/
def res581G (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 len maxP : Nat)
    (Z : IProp GF) (W : UInt32 → UInt32 → IProp GF) (p : UInt32) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
      n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
    ((⌜p ≠ 0⌝ ∗ ∃ v : UInt32, n ↦[i32][ 1074896 ] v ∗ n ↦[wmlength] len ∗ W p v) ∨
     (⌜p = 0 ∧ ¬ GrowOk len (some maxP) (cellPages (wordsOf size) al).toNat⌝ ∗
       n ↦[i32][ 1074896 ] 0 ∗ n ↦[wmlength] len ∗ vt n 1057464 idx ta a578 ∗ Z) ∨
     (Z ∗ n ↦[wmlength] (len + (cellPages (wordsOf size) al).toNat * pageSize) ∗ n ↦[i32][ len + 4 ] 0 ∗
      ∃ rest : List UInt8, ⌜rest.length = (cellPages (wordsOf size) al).toNat * 65536 - 12⌝ ∗
        post1 n (wordsOf size) al 1074896 (UInt32.ofNat len) (chunkEnd len size al) 0 true rest
          1057464 idx ta a578 [] [.i32 p])))

set_option maxHeartbeats 8000000 in
theorem f581_gen (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al h idx : UInt32) (k : Nat) (len maxP : Nat) (o1 o2 o4 : List UInt8)
    (PW Z : IProp GF) (W : UInt32 → UInt32 → IProp GF)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    n ↪[wmlimit] some maxP ∗ walkSpec cfg lim (d + 1) inst mi Cg n sp size al h idx ta (A 578) PW Z W ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          pre581G n g gt sp h len o1 o2 o4 ∗ PW))
        (fun _ => 910 * cfg.regularOpCost + cfg.linearOpBaseCost +
          cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗
          res581G n g gt sp size al idx ta (A 578) len maxP Z W p)) := by
  iintro ⟨#Hm, #HWalk, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HR, HP⟩ Hc
  subst hargs
  iunfold pre581G at HR
  icases HR with ⟨Hg, Ho1, Ho2, Ho4, Hh, Hl⟩
  have hglob := hm.glob
  have hmem := hm.mem
  have eS : (UInt32.ofNat (sp.toNat - 16)).toNat = sp.toNat - 16 := by
    have := sp.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  have hS : sp - 16 = UInt32.ofNat (sp.toNat - 16) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega), eS]; simp
  have eT : (UInt32.ofNat (sp.toNat - 4)).toNat = sp.toNat - 4 := by
    have := sp.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  have hT : UInt32.ofNat (sp.toNat - 16) + 12 = UInt32.ofNat (sp.toNat - 4) := by
    apply UInt32.toNat_inj.mp; have := sp.toNat_lt
    rw [UInt32.toNat_add, eS, eT]; simp; omega
  have hS16 : UInt32.ofNat (sp.toNat - 16) + 16 = sp := by
    apply UInt32.toNat_inj.mp; have := sp.toNat_lt
    rw [UInt32.toNat_add]; simp only [UInt32.toNat_ofNat']; simp; omega
  ihave Ho1 := memBytes_addr (show sp.toNat - 16 = (UInt32.ofNat (sp.toNat - 16)).toNat by omega) $$ Ho1
  ihave Ho2 := memBytes_addr (show sp.toNat - 12 = (UInt32.ofNat (sp.toNat - 16)).toNat + 4 by omega) $$ Ho2
  ihave Ho4 := memBytes_addr (show sp.toNat - 4 = (UInt32.ofNat (sp.toNat - 16)).toNat + 12 by omega) $$ Ho4
  have hE := Hold.mk (show (UInt32.ofNat (sp.toNat - 16)).toNat + 12 = (UInt32.ofNat (sp.toNat - 4)).toNat by omega)
  have hsz0 : size ≠ 0 := by intro h; subst h; simp at hsize
  have hW := Hold.mk (show (wordsOf size).toNat = (size.toNat + 3) / 4 by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega)
  have hW570 := Hold.mk (show (size + 4 + 4294967295) / 4 = wordsOf size by
    apply UInt32.toNat_inj.mp; rw [hW.get, UInt32.toNat_div, UInt32.toNat_add, UInt32.toNat_add]; simp; omega)
  have hsp' := Hold.mk hsp
  have hS16' := Hold.mk hS16
  clear eS eT hsp hS16
  have hp32 : types[32]!.params.length = 1 := by rfl
  have hp34 : types[34]!.params.length = 5 := by rfl
  have hp45 : types[45]!.params.length = 4 := by rfl
  have h570 := hm.funcs 570 (by decide)
  have h580 := hm.funcs 580 (by decide)
  have h577 := hm.funcs 577 (by decide)
  simp only [f581]
  mstep [Hg]; mstep; mstep
  rw [hS]
  mstep; mstep [Hg]
  mstep; mstep; mstep
  mstep_taken with (simp [Numeric.bool, hsz0])
  mstep
  mcall (f570_spec cfg lim (d + 1) types[32]! (by rfl) inst mi (A 568) (hm.funcs 568 (by decide))
      types[13]! (by rfl) (by rfl) (by omega) Cg size (by omega))
    with (simp [activationGas, entryLocals, f570, hp32]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  rw [hW570.get]
  mstep; mstep; mstep; mstep [Hh]; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep; mstep
  rw [hT]
  ihave Ho4 := memBytes_addr hE.get $$ Ho4
  mstep; mstep
  mcall HWalk using [Ho4 HP]
    with (simp [activationGas, entryLocals, f580, hp34]; omega)
  · iframe Ho4 HP
  iunfold walkQ at HQ
  icases HQ with ⟨%r, %hrs, HQ⟩
  subst hrs
  icases HQ with (⟨%hr0, Ho4, Hvt, HZ⟩ | ⟨%hr, %v, Ho4, HWr⟩)
  swap
  · -- the first walk succeeded: `ALLOC := slot`, return
    mstep
    mstep_taken with (exact hr)
    ihave Ho4 := memBytes_addr hE.get.symm $$ Ho4
    mstep; mstep; mstep [Ho4]; mstep [Hh]
    mstep; mstep; mstep; mstep [Hg]; mstep
    rw [hS16'.get, htype]
    mcredits R
    iframe Hc
    iexists r
    isplitr; · ipureintro; rfl
    iunfold res581G
    iframe Hg
    isplitl [Ho1 Ho2 Ho4]
    · iexists _, _, _
      ihave Ho1 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat = sp.toNat - 16 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho1
      ihave Ho2 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 4 = sp.toNat - 12 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho2
      ihave Ho4 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 12 = sp.toNat - 4 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho4
      iframe Ho1 Ho2 Ho4
      ipureintro; simp [bytes32, ho1, ho2]
    ileft
    isplitr; · ipureintro; exact hr
    iexists v
    iframe Hh Hl HWr
  subst hr0
  mstep
  mstep_not_taken
  mstep; mstep; mstep; mstep
  have hal20 : al.toNat < 2 ^ 20 := by
    rw [hal]; exact Nat.pow_lt_pow_right (by omega) hk
  mcall (f577_lim cfg lim (d + 1) types[45]! (by rfl) inst mi n hmem (A 572) (A 569) (A 568) (A 573) (A 574)
      (hm.funcs 572 (by decide)) (hm.funcs 569 (by decide)) (hm.funcs 568 (by decide))
      (hm.funcs 573 (by decide)) (hm.funcs 574 (by decide)) types[32]! types[32]! types[13]! types[32]! types[0]!
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by omega) Cg
      (UInt32.ofNat (sp.toNat - 16)) 1057464 (wordsOf size) al len maxP o1 o2
      (by rw [hW.get]; omega) hal20 (by have := hsp'.get; have := sp.toNat_lt; simp only [UInt32.toNat_ofNat']; omega)
      hlen0 ho1 ho2) using [Ho1 Ho2 Hl]
    with (simp [activationGas, entryLocals, f577, hp45]; omega)
  · iframe Ho1 Ho2 Hl
  iunfold postL at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  have hPb := Hold.mk (cellPages_bounds (wordsOf size) al (by rw [hW.get]; omega) hal20)
  generalize hCP : cellPages (wordsOf size) al = CP at *
  have hCP' := Hold.mk hCP
  clear hCP
  mcredits (348 * cfg.regularOpCost + R)
  icases HQ with (⟨Ho1, Ho2, Hl, HW0, HW1, HNF, Hrest⟩ | ⟨%hfail, Ho1, Ho2, Hl⟩)
  swap
  · mstep; mstep; mstep; mstep [Ho1]
    mstep_taken with (simp [Numeric.bool])
    ihave Ho4 := memBytes_addr hE.get.symm $$ Ho4
    mstep; mstep; mstep [Ho4]; mstep [Hh]
    mstep; mstep; mstep; mstep [Hg]; mstep
    rw [hS16'.get, htype]
    mcredits R
    iframe Hc
    iexists 0
    isplitr; · ipureintro; rfl
    iunfold res581G
    iframe Hg
    isplitl [Ho1 Ho2 Ho4]
    · iexists _, _, _
      ihave Ho1 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat = sp.toNat - 16 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho1
      ihave Ho2 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 4 = sp.toNat - 12 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho2
      ihave Ho4 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 12 = sp.toNat - 4 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho4
      iframe Ho1 Ho2 Ho4
      ipureintro; simp [bytes32]
    iright; ileft
    iframe Hh Hl Hvt HZ
    ipureintro; rw [hCP'.get]; exact ⟨rfl, hfail⟩
  -- memory.grow succeeded: the fresh cell `len` goes on the list and 580 walks it
  have hP1 := hPb.get.1
  have hP2 := hPb.get.2
  have hlenN : (UInt32.ofNat len).toNat = len := by
    simp only [UInt32.toNat_ofNat']; omega
  have hNX : (UInt32.ofNat len + CP <<< 16).toNat = len + CP.toNat * 65536 := by
    rw [UInt32.toNat_add, hlenN, shl16_toNat CP hP2]; omega
  icases Hrest with ⟨%rest, %⟨hrl, -⟩, Hrest⟩
  ihave HW0 := memBytes_addr hlenN.symm $$ HW0
  ihave HNF := memBytes_addr (show len + 8 = (UInt32.ofNat len).toNat + 8 by omega) $$ HNF
  ihave Hrest := memBytes_addr (show len + 12 = (UInt32.ofNat len).toNat + 12 by omega) $$ Hrest
  have hF := Hold.mk (And.intro hlenN hNX)
  clear hlenN hNX
  ihave Ho4 := memBytes_addr hE.get.symm $$ Ho4
  mstep; mstep; mstep; mstep [Ho1]
  mstep_not_taken
  mstep; mstep [Ho2]; mstep; mstep; mstep [Ho4]; mstep [HNF]
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep
  rw [hT]
  ihave Ho4 := memBytes_addr hE.get $$ Ho4
  mstep; mstep
  rw [show (UInt32.ofNat 0 : UInt32) = 0 from rfl]
  mcall (f580_one cfg lim (d + 1) types[34]! (by rfl) inst mi n hmem (A 572) (A 576) (A 574) (A 578) ta
      (hm.funcs 572 (by decide)) (hm.funcs 576 (by decide)) (hm.funcs 574 (by decide)) hm.table
      types[32]! types[32]! types[0]! (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rw [hm.types]; rfl) (by rw [hm.types]; rfl) (by omega) Cg
      (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464 idx (UInt32.ofNat len)
      (UInt32.ofNat len + CP <<< 16) 0 true rest k hal (by omega)
      (by rw [hW.get]; omega) (by rw [hW.get]; omega)
      (by rw [hF.get.1]; omega) (and3_of_mod4 _ (by rw [hF.get.1]; omega))
      (and3_of_mod4 _ (by rw [hF.get.2]; omega)) (by rw [hF.get.1, hF.get.2]; omega)
      (by rw [hF.get.2]; omega) (by rw [hF.get.1, hF.get.2]; omega)) using [Ho4 HW0 HNF Hrest Hvt]
    with (simp [activationGas, entryLocals, f580, hp34]; omega)
  · rw [hm.types]; mpersist
  · iunfold oneRes
    rw [nextW_true, show w0 (UInt32.ofNat len + CP <<< 16) true = UInt32.ofNat len + CP <<< 16 ||| 2 from rfl]
    iframe Ho4 HW0 HNF Hrest Hvt
  ihave HQ := post1_move n _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1074896 $$ HQ
  icases HQ with ⟨%v, %r, %hrs, Hsl, Hk⟩
  subst hrs
  mstep
  ihave Hsl := memBytes_addr hE.get.symm $$ Hsl
  mstep; mstep; mstep [Hsl]; mstep [Hh]
  ihave HP := Hk $$ Hh
  mstep; mstep; mstep; mstep [Hg]; mstep
  rw [hS16'.get, htype]
  mcredits R
  iframe Hc
  iexists r
  isplitr; · ipureintro; rfl
  iunfold res581G
  iframe Hg
  isplitl [Ho1 Ho2 Hsl]
  · iexists _, _, _
    ihave Ho1 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat = sp.toNat - 16 by
      have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho1
    ihave Ho2 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 4 = sp.toNat - 12 by
      have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho2
    ihave Hsl := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 12 = sp.toNat - 4 by
      have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Hsl
    iframe Ho1 Ho2 Hsl
    ipureintro; simp [bytes32]
  iright; iright
  have hc := hCP'.get
  rw [i64_zero_hi] at *
  simp only [chunkEnd]
  rw [hc]
  iframe HZ Hl HW1
  iexists rest
  iframe HP
  ipureintro; exact hrl

/-- `__rust_alloc(size, align)` (310 → 236 → 581) for any first walk: `f581_gen` through
`AllocWrap`, 30 more `regular_op_cost`s. -/
theorem f310_gen (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al h idx : UInt32) (k : Nat) (len maxP : Nat) (o1 o2 o4 : List UInt8)
    (PW Z : IProp GF) (W : UInt32 → UInt32 → IProp GF)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    n ↪[wmlimit] some maxP ∗ walkSpec cfg lim (d + 1 + 1 + 1) inst mi Cg n sp size al h idx ta (A 578) PW Z W ∗
      A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗
          (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
            (pre581G n g gt sp h len o1 o2 o4 ∗ PW))))
        (fun _ => 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)))
        (fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ res581G n g gt sp size al idx ta (A 578) len maxP Z W p)) := by
  iintro ⟨#Hm, #HWalk, #H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩
  iapply (AllocWrap.f310_of_f236 cfg lim d type htype inst mi (A 236) (hm.funcs 236 (by decide))
    types[13]! (by rfl) (by rfl) (by omega) Cg _ _ (res581G n g gt sp size al idx ta (A 578) len maxP Z W) size al)
  isplitr; · iexact H236
  isplitr; · iexact Hi
  imodintro
  iapply (AllocWrap.f236_spec cfg lim (d + 1) types[13]! (by rfl) inst mi (A 581) (hm.funcs 581 (by decide))
    types[15]! (by rfl) (by rfl) (by omega) Cg
    (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ (pre581G n g gt sp h len o1 o2 o4 ∗ PW)))
    (fun _ => 910 * cfg.regularOpCost + cfg.linearOpBaseCost +
      cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
    (res581G n g gt sp size al idx ta (A 578) len maxP Z W) size al)
  isplitr; · iexact H581
  isplitr; · iexact Hi
  imodintro
  have h581 := f581_gen (GF := GF) cfg lim (d + 1 + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    sp size al h idx k len maxP o1 o2 o4 PW Z W hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom
  iapply h581
  iframe Hm HWalk
  mpersist

end Spec

end WNear.Binary.AllocGen
