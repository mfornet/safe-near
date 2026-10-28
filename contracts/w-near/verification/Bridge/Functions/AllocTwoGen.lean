import Bridge.Functions.AllocGen

/-!
# `WeeAlloc::alloc` (581) and `__rust_alloc` (310) when the first walk succeeds (M4)

`AllocGen.f581_gen` takes the first walk's specification at 300 `regular_op_cost`s. A walk over
two free cells costs more, up to about 480 when it succeeds; when the first walk succeeds 581
neither grows memory nor walks again, so the 910 of `f581_gen` still bound the whole call.
`f581_succ` is `f581_gen` for a first walk of cost `Kw ≤ 600` that does not fail
(`walkSpecK`, its failure leftovers `False`), with the same cost and result; `f310_succ` through
`AllocWrap`, as `f310_gen`.
-/

namespace WNear.Binary.AllocGen

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocLeaves WNear.Binary.AllocFirstFit WNear.Binary.AllocNewCell
open WNear.Binary.AllocAlloc (wordsOf chunkEnd post1_move)
open WNear.Binary.AllocLimit (f577_lim postL)
open WNear.Binary.Interface (IfaceMod)
set_option maxRecDepth 20000

section Succ

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `walkSpec` at the cost `Kw`, a walk that does not fail. -/
abbrev walkSpecK (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (Cg : Nat)
    (n : Nat) (sp size al h idx : UInt32) (ta a578 : Nat) (PW : IProp GF)
    (W : UInt32 → UInt32 → IProp GF) (Kw : Nat) : IProp GF :=
  MFunSpec cfg lim d types[34]! inst mi f580 Cg
    (fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
      .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] h ∗ PW))
    (fun _ => Kw)
    (walkQ n (UInt32.ofNat (sp.toNat - 4)).toNat idx ta a578 iprop(⌜False⌝) W)
set_option maxHeartbeats 8000000 in
theorem f581_succ (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al h idx : UInt32) (k : Nat) (len maxP : Nat) (o1 o2 o4 : List UInt8)
    (PW : IProp GF) (W : UInt32 → UInt32 → IProp GF) (Kw : Nat) (hKw : Kw ≤ 600 * cfg.regularOpCost)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    n ↪[wmlimit] some maxP ∗ walkSpecK cfg lim (d + 1) inst mi Cg n sp size al h idx ta (A 578) PW W Kw ∗
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
          res581G n g gt sp size al idx ta (A 578) len maxP iprop(⌜False⌝) W p)) := by
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
  icases HQ with (⟨%hr0, Ho4, Hvt, %hZ⟩ | ⟨%hr, %v, Ho4, HWr⟩)
  · exact hZ.elim
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

/-- `__rust_alloc(size, align)` (310 → 236 → 581) for a first walk of cost `Kw ≤ 600` that does not
fail: `f581_succ` through `AllocWrap`, as `f310_gen`. -/
theorem f310_succ (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al h idx : UInt32) (k : Nat) (len maxP : Nat) (o1 o2 o4 : List UInt8)
    (PW : IProp GF) (W : UInt32 → UInt32 → IProp GF) (Kw : Nat) (hKw : Kw ≤ 600 * cfg.regularOpCost)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    n ↪[wmlimit] some maxP ∗ walkSpecK cfg lim (d + 1 + 1 + 1) inst mi Cg n sp size al h idx ta (A 578) PW W Kw ∗
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
        (fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ res581G n g gt sp size al idx ta (A 578) len maxP iprop(⌜False⌝) W p)) := by
  iintro ⟨#Hm, #HWalk, #H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩
  iapply (AllocWrap.f310_of_f236 cfg lim d type htype inst mi (A 236) (hm.funcs 236 (by decide))
    types[13]! (by rfl) (by rfl) (by omega) Cg _ _ (res581G n g gt sp size al idx ta (A 578) len maxP iprop(⌜False⌝) W) size al)
  isplitr; · iexact H236
  isplitr; · iexact Hi
  imodintro
  iapply (AllocWrap.f236_spec cfg lim (d + 1) types[13]! (by rfl) inst mi (A 581) (hm.funcs 581 (by decide))
    types[15]! (by rfl) (by rfl) (by omega) Cg
    (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ (pre581G n g gt sp h len o1 o2 o4 ∗ PW)))
    (fun _ => 910 * cfg.regularOpCost + cfg.linearOpBaseCost +
      cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
    (res581G n g gt sp size al idx ta (A 578) len maxP iprop(⌜False⌝) W) size al)
  isplitr; · iexact H581
  isplitr; · iexact Hi
  imodintro
  have h581 := f581_succ (GF := GF) cfg lim (d + 1 + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    sp size al h idx k len maxP o1 o2 o4 PW W Kw hKw hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom
  iapply h581
  iframe Hm HWalk
  mpersist

end Succ

end WNear.Binary.AllocGen
