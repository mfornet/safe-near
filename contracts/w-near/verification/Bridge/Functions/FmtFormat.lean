import Bridge.Functions.FmtWriteN
import Bridge.Functions.VecWithCap
import Bridge.Functions.ResultExpect
import Binary.Code.Part14

/-!
# `alloc::fmt::format` (846) (M8)

`format!(…)` is `alloc::fmt::format(&mut out, &args)` (846) on `Arguments { pieces, fmt: None, args }`:

```
846  sp -= 32
     L = Σ pieces[i].len                                  (the capacity loop, 8 bytes a piece)
     args.len ≠ 0, L > 15 ⇒ cap = 2·L                       (estimated_capacity)
     q = __rust_alloc(cap, 1) (310)                          cap ≠ 0
     out = String { ptr: q, cap, len: 0 }
     *(sp + 4) = out; the Arguments copied to sp + 8
     core::fmt::write(sp + 4, 1066728, sp + 8) (872)        Ok ⇒ sp += 32
```

`f846_gen` is parametric in 872's specification (`hS`, for every block `q` the allocator may
return), as `FmtWrite.f746_gen` is: the caller instantiates it with `FmtWriteN.f872_gen` and the
sink `<&mut String as Write>::write_str` (1066728's slot 12, table entry 189, function 840).

The capacity loop is `iter846` (the loop's exit is a continuation, `exit846`, carried by the
invariant, as in `FmtWriteN`). The piece lengths are read through the accessor `hMl` of the
pieces array `M`; `psum plen k = L`.

Cost (`cost846`): `110` `regular_op_cost`s, `16` per piece, the allocator (`costAllocF`) and 872
with their activations.
-/

namespace WNear.Binary.FmtFormat

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtWriteN (argsN)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.VecWithCap (costAllocF okG f310_roomG)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)

/-- The sum of the first `i` piece lengths. -/
def psum (plen : Nat → UInt32) : Nat → Nat
  | 0 => 0
  | i + 1 => psum plen i + (plen i).toNat

theorem psum_mono (plen : Nat → UInt32) {i j : Nat} (h : i ≤ j) : psum plen i ≤ psum plen j := by
  induction j with
  | zero => simp at h; subst h; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h1 | h1
    · have := ih (by omega); simp only [psum]; omega
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

theorem shl3_toNat (k : UInt32) (h : 8 * k.toNat < 2 ^ 32) : (k <<< (3 % 32)).toNat = 8 * k.toNat := by
  rw [UInt32.toNat_shiftLeft]
  simp [Nat.shiftLeft_eq]
  omega

theorem sub8_toNat (x : UInt32) (h : 8 ≤ x.toNat) : (x + 4294967288).toNat = x.toNat - 8 := by
  have e : x + 4294967288 = x - 8 := by
    rw [UInt32.sub_eq_add_neg]; rfl
  rw [e, UInt32.toNat_sub_of_le]
  · simp
  · simp [UInt32.le_iff_toNat_le]; omega

/-- A fact kept from the step tactics. -/
def HideP (p : Prop) : Prop := p

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 846's frame in the capacity loop. -/
abbrev fr846 (inst : Nat) (mi : ModuleInst) (out ar sp pp k l5 l6 l7 : UInt32) : Frame :=
  ⟨#[.i32 out, .i32 ar, .i32 sp, .i32 pp, .i32 k, .i32 l5, .i32 l6, .i32 l7], inst, mi⟩

/-- The capacity loop's body. -/
abbrev body846 : List Instr :=
  [.local_get 7, .load .i32 none { align := 2, offset := 0 }, .local_get 6, .i32_binop .add, .local_set 6,
    .local_get 7, .i32_const 8, .i32_binop .add, .local_set 7, .local_get 5, .i32_const 4294967288,
    .i32_binop .add, .local_tee 5, .br_if 0]

/-- The loop's exit: from any locals with the sum `L`, `R0` credits and `B`. -/
def exit846 (inst : Nat) (mi : ModuleInst) (Cg R0 : Nat) (out ar sp pp k : UInt32) (L : Nat) (B : IProp GF)
    (Φ : Post NearState GF) : IProp GF :=
  iprop(∀ l5 l6 l7, ⌜UInt32.toNat l6 = L⌝ -∗ credits Cg R0 -∗ B -∗
    Φ.normal [] (fr846 inst mi out ar sp pp k l5 l6 l7))

/-- The capacity loop's invariant at the piece `i < k`. -/
def inv846 (inst : Nat) (mi : ModuleInst) (Cg c R0 : Nat) (out ar sp pp k : UInt32) (plen : Nat → UInt32)
    (Res : IProp GF) : List Value → Frame → IProp GF := fun X fr =>
  iprop(∃ (i : Nat) (l5 l6 l7 : UInt32), ⌜X = [] ∧ fr = fr846 inst mi out ar sp pp k l5 l6 l7 ∧
      i < k.toNat ∧ l5.toNat = 8 * (k.toNat - i) ∧ l6.toNat = psum plen i ∧ l7.toNat = pp.toNat + 4 + 8 * i⌝ ∗
    credits Cg ((k.toNat - i) * (16 * c) + R0) ∗ Res)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **One iteration of the capacity loop**: `L += pieces[i].len`, back to the loop or out of it. -/
theorem iter846 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out ar sp pp k : UInt32) (plen : Nat → UInt32) (L : Nat)
    (hL : psum plen k.toNat = L) (hL28 : L < 2 ^ 28) (hpp : pp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32)
    (M : IProp GF) (hMl : ∀ j, j < k.toNat → M ⊢ n ↦[i32][ pp.toNat + 8 * j + 4 ] plen j ∗
      (n ↦[i32][ pp.toNat + 8 * j + 4 ] plen j -∗ M))
    (R0 : Nat) (Rest : IProp GF) (Φ : Post NearState GF) (es : List Instr) (hes : es = body846) :
    ⊢ □ ∀ (X : List Value) (fr : Frame),
      inv846 inst mi Cg cfg.regularOpCost R0 out ar sp pp k plen
        iprop(M ∗ Rest ∗ exit846 inst mi Cg R0 out ar sp pp k L iprop(M ∗ Rest) Φ) X fr -∗
      mwpi cfg lim d fr X es (Post.mloop cfg Cg 0 []
        (inv846 inst mi Cg cfg.regularOpCost R0 out ar sp pp k plen
          iprop(M ∗ Rest ∗ exit846 inst mi Cg R0 out ar sp pp k L iprop(M ∗ Rest) Φ)) Φ) := by
  subst hes
  imodintro
  iintro %X %fr HI
  iunfold inv846 at HI
  icases HI with ⟨%i, %l5, %l6, %l7, %⟨hX, hfr, hi, h5, h6, h7⟩, Hc, HM, HR, HEx⟩
  subst hX hfr
  icases hMl i hi $$ HM with ⟨Hl, HMw⟩
  rw [show (k.toNat - i) * (16 * cfg.regularOpCost) + R0 =
    16 * cfg.regularOpCost + ((k.toNat - (i + 1)) * (16 * cfg.regularOpCost) + R0) by
      rw [show k.toNat - i = (k.toNat - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]; omega]
  generalize hZ : (k.toNat - (i + 1)) * (16 * cfg.regularOpCost) + R0 = Z
  have hl7 : l7.toNat + 0 = pp.toNat + 8 * i + 4 := by omega
  have hH : HideP (psum plen k.toNat = L ∧ l6.toNat = psum plen i) := ⟨hL, h6⟩
  clear hL h6
  mstep
  mstep [Hl] with exact hl7
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  obtain ⟨hL, h6⟩ := hH
  have hmono := psum_mono plen (show i + 1 ≤ k.toNat by omega)
  have hpsum : psum plen (i + 1) = psum plen i + (plen i).toNat := rfl
  have h5' := sub8_toNat l5 (by omega)
  generalize l5 + 4294967288 = l5' at h5' ⊢
  have h6' : (plen i + l6).toNat = psum plen (i + 1) := by
    rw [UInt32.toNat_add, h6, hpsum]; have := (plen i).toNat_lt; omega
  generalize plen i + l6 = l6' at h6' ⊢
  have h7' : (l7 + 8).toNat = pp.toNat + 4 + 8 * (i + 1) := by
    rw [UInt32.toNat_add, h7]; simp; omega
  generalize l7 + 8 = l7' at h7' ⊢
  by_cases hlast : i + 1 = k.toNat
  · have hz : l5' = 0 := UInt32.toNat_inj.mp (by rw [h5']; simp; omega)
    subst hz
    repeat mstep
    simp only [Post.mloop]
    iapply pay_intro'
    iframe Hc
    isplitr
    · ipureintro; omega
    inext
    iintro Hc
    iunfold exit846 at HEx
    rw [List.nil_append]
    mcredits R0
    iapply HEx $$ %0 %l6' %l7' %(by rw [h6', hlast, hL]) Hc
    ihave HM := HMw $$ Hl
    iframe HM HR
  · have hnz : l5' ≠ 0 := by
      intro h; subst h; simp at h5'; omega
    repeat mstep
    simp only [Post.mloop]
    iapply pure_pay_intro'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨by simp, by omega⟩
    inext
    iintro Hc
    ihave HM := HMw $$ Hl
    iunfold inv846
    iexists i + 1, l5', l6', l7'
    isplitr
    · ipureintro
      refine ⟨by simp, rfl, by omega, by omega, h6', h7'⟩
    isplitl [Hc]
    · iapply credits_le; iframe Hc; ipureintro; omega
    iframe HM HR HEx

/-- The resources of 846 aside from the pieces array, carried by the capacity loop. -/
def Rest846 (n g : Nat) (gt : GlobalType) (s ar pp argp k : UInt32) (junk : List UInt8) (out idx : UInt32)
    (ta a578 maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (P : IProp GF) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ stk n (s.toNat - 48) 48 ∗ n ↦[i32][ ar.toNat ] pp ∗
    n ↦[i32][ ar.toNat + 4 ] k ∗ n ↦[i32][ ar.toNat + 8 ] 0 ∗ n ↦[i32][ ar.toNat + 16 ] argp ∗
    n ↦[i32][ ar.toNat + 20 ] k ∗ n ↦[wms][ ar.toNat + 12 ] junk ∗ stk n out.toNat 12 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗ P)

/-- The capacity `2·L`. -/
abbrev capOf (L : Nat) : UInt32 := UInt32.ofNat (2 * L)

/-- The `String` `(q, cap, 0)` at `out`. -/
def strNew (n : Nat) (out q cap : UInt32) : IProp GF :=
  iprop(n ↦[i32][ out.toNat ] q ∗ n ↦[i32][ out.toNat + 4 ] cap ∗ n ↦[i32][ out.toNat + 8 ] 0)

/-- The cost of 846 on `k` pieces of total length `L`, the activation excluded. -/
noncomputable def cost846 (cfg : WasmConfig) (F k L K : Nat) : Nat :=
  110 * cfg.regularOpCost + k * (16 * cfg.regularOpCost) +
    activationGas cfg.regularOpCost (entryLocals f310 [.i32 0, .i32 0]) + costAllocF cfg F (capOf L) +
    activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) + K

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`alloc::fmt::format(out, ar)`** (846) on `k ≥ 1` pieces of total length `L ≥ 16` and `k`
arguments: a `String` of capacity `2·L` allocated, then `core::fmt::write` into it (`hS`, for the
block `q` the allocator returns), `Ok`. -/
theorem f846_gen (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s out ar pp argp k : UInt32) (junk : List UInt8) (hjunk : junk.length = 4) (hk0 : 0 < k.toNat)
    (hs : 48 ≤ s.toNat) (har : ar.toNat + 24 ≤ 2 ^ 32) (hpp : pp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32)
    (plen : Nat → UInt32) (L : Nat) (hL : psum plen k.toNat = L) (hL16 : 16 ≤ L) (hL28 : 2 * L < 2 ^ 28)
    (M : IProp GF) (hMl : ∀ j, j < k.toNat → M ⊢ n ↦[i32][ pp.toNat + 8 * j + 4 ] plen j ∗
      (n ↦[i32][ pp.toNat + 8 * j + 4 ] plen j -∗ M))
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (idx : UInt32) (hr : roomFor hl maxP (capOf L))
    (hF : okG F) (C : IProp GF) [Persistent C] (P : IProp GF) (Qf : UInt32 → IProp GF) (K : Nat)
    (hC : C ⊢ inst ↪[inst] mi ∗ allocCode n maxP inst mi A ∗ A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗
      A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575 ∗
      A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872)
    (hS : ∀ q : UInt32, q ≠ 0 → C ⊢ MFunSpec cfg lim (d + 1) types[15]! inst mi f872 Cg
      (fun args => iprop(⌜args = [.i32 (s - 32 + 4), .i32 1066728, .i32 (s - 32 + 8)]⌝ ∗
        g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ argsN n (s - 32 + 8) pp argp k ∗ n ↦[i32][ (s - 32 + 4).toNat ] out ∗
        stk n ((s - 32).toNat - 16) 16 ∗ M ∗ strNew n out q (capOf L) ∗ vt n 1057464 idx ta (A 578) ∗
        (∃ len', ⌜len' = hl ∨ len' = hl + (cellPages (wordsOf (capOf L)) 1).toNat * 65536⌝ ∗
          heapInv n maxP len' ((q.toNat, (capOf L).toNat) :: live) F ∗ block n q.toNat (capOf L).toNat) ∗ P))
      (fun _ => K)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ argsN n (s - 32 + 8) pp argp k ∗
        n ↦[i32][ (s - 32 + 4).toNat ] out ∗ stk n ((s - 32).toNat - 16) 16 ∗ Qf q))) :
    C ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f846 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsN n ar pp argp k ∗ n ↦[wms][ ar.toNat + 12 ] junk ∗ M ∗
          stk n out.toNat 12 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗ P))
        (fun _ => cost846 cfg F k.toNat L K)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗
          argsN n ar pp argp k ∗ n ↦[wms][ ar.toNat + 12 ] junk ∗ ∃ q, Qf q)) := by
  iintro #C
  ihave ⟨#Hi, #HA, #H236, #H581, #H575, #H310, #H872⟩ := hC $$ C
  have hn := hm.mem
  have hg := hm.glob
  have ha310 := hm.funcs 310 (by decide)
  have ha872 := hm.funcs 872 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hsp : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlt := s.toNat_lt
  have h4 : (s - 32 + 4).toNat = (s - 32).toNat + 4 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have h8 : (s - 32 + 8).toNat = (s - 32).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  simp only [cost846]
  have hA310 : activationGas cfg.regularOpCost (entryLocals f310 [.i32 0, .i32 0]) = 10 * cfg.regularOpCost := by
    mstep_norm_full
  have hA872 : activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) = 14 * cfg.regularOpCost := by
    mstep_norm_full
  rw [hA310, hA872]
  generalize hCA : costAllocF cfg F (capOf L) = CA
  generalize hW : k.toNat * (16 * cfg.regularOpCost) = W
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HA, HJ, HM, HO, Hvt, Hinv, HP⟩
  subst hargs
  iunfold argsN at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  simp only [f846]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep [A0]
  repeat mstep
  mstep [A4]
  repeat mstep
  have hk8 := shl3_toNat k (by omega)
  generalize k <<< (3 % 32) = k8 at hk8 ⊢
  have hk8ne : k8 ≠ 0 := by intro h; subst h; simp at hk8; omega
  repeat mstep
  iapply FmtWriteN.mwpi_loop_dep (Cg := Cg)
    (R := W + (88 * cfg.regularOpCost + 10 * cfg.regularOpCost + CA + 14 * cfg.regularOpCost + K + R))
    (I := fun Φ => inv846 inst mi Cg cfg.regularOpCost (88 * cfg.regularOpCost + 10 * cfg.regularOpCost + CA + 14 * cfg.regularOpCost + K + R)
      out ar (s - 32) pp k plen
      iprop(M ∗ Rest846 n g gt s ar pp argp k junk out idx ta (A 578) maxP hl live F P ∗
        exit846 inst mi Cg (88 * cfg.regularOpCost + 10 * cfg.regularOpCost + CA + 14 * cfg.regularOpCost + K + R) out ar (s - 32) pp k L
          iprop(M ∗ Rest846 n g gt s ar pp argp k junk out idx ta (A 578) maxP hl live F P) Φ)) _ _ rfl
  isplitr
  · ihave #It := iter846 cfg lim d inst mi n hn Cg out ar (s - 32) pp k plen L hL (by omega) hpp M hMl
      (88 * cfg.regularOpCost + 10 * cfg.regularOpCost + CA + 14 * cfg.regularOpCost + K + R)
      (Rest846 n g gt s ar pp argp k junk out idx ta (A 578) maxP hl live F P) _ body846 rfl
    imodintro
    iintro %X %l HI
    iapply It $$ HI
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  inext
  iintro Hc
  iunfold inv846
  iexists 0, k8, 0, pp + 4
  isplitr
  · ipureintro
    refine ⟨rfl, rfl, hk0, by omega, rfl, ?_⟩
    rw [UInt32.toNat_add]; simp; omega
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; rw [Nat.sub_zero, hW]
  isplitl [HM]; · iexact HM
  isplitl [Hg Hs A0 A4 A8 A16 A20 HJ HO Hvt Hinv HP]
  · iunfold Rest846
    iframe Hg Hs A0 A4 A8 A16 A20 HJ HO Hvt Hinv HP
  iunfold exit846
  iintro %l5 %l6 %l7 %h6 Hc ⟨HM, HR⟩
  iunfold Rest846 at HR
  icases HR with ⟨Hg, Hs, A0, A4, A8, A16, A20, HJ, HO, Hvt, Hinv, HP⟩
  mctrl_norm
  repeat mpay
  repeat mstep
  mstep [A20]
  have hkne : k ≠ 0 := by intro h; subst h; simp at hk0
  have hk0b : Numeric.bool (k == 0) = 0 := by simp [Numeric.bool, hkne]
  have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u l6 15) = 1 := by
    simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
  repeat mstep
  have hc2 : (l6 + l6).toNat = 2 * L := by rw [UInt32.toNat_add, h6]; omega
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (l6 + l6) l6) = 1 := by
    simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
  rw [hge]; clear hge
  have hcap : l6 + l6 = capOf L := UInt32.toNat_inj.mp (by rw [hc2]; simp; omega)
  rw [hcap]
  have hcapN : (capOf L).toNat = 2 * L := by simp; omega
  have hle : Numeric.bool (Numeric.irelop32 IRelOp.le_s (capOf L) 4294967295) = 0 := by
    exact VecFromElem.les_neg1 _ (by omega)
  have hcne : capOf L ≠ 0 := by intro h; rw [h] at hcapN; simp at hcapN; omega
  repeat mstep
  -- the allocation
  ihave Hs := stk_addr (show s.toNat - 48 = (s - 32).toNat - 16 by omega) $$ Hs
  icases stk_split n ((s - 32).toNat - 16) 16 32 $$ Hs with ⟨Lo, Fr⟩
  icases VecFromElem.stk16 n ((s - 32).toNat - 16) $$ Lo with ⟨L0, L4, L8, L12⟩
  iunfold stk at L0 L4 L12
  icases L0 with ⟨%o1, %ho1, L0⟩
  icases L4 with ⟨%o2, %ho2, L4⟩
  icases L12 with ⟨%o4, %ho4, L12⟩
  ihave L4 := memBytes_addr (show (s - 32).toNat - 16 + 4 = (s - 32).toNat - 12 by omega) $$ L4
  ihave L12 := memBytes_addr (show (s - 32).toNat - 16 + 12 = (s - 32).toNat - 4 by omega) $$ L12
  ihave #S310 := f310_roomG cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
    (capOf L) idx maxP hl live F o1 o2 o4 (by omega) (by omega) (by omega) ho1 ho2 ho4 hr hF $$ [HA H236 H581 H575]
  · iframe HA H236 H581 H575
  mcall S310 using [Hg L0 L4 L12 Hvt Hinv]
  · iframe Hg L0 L4 L12 Hvt Hinv
  icases HQ with ⟨%q, %⟨hrs, hq0, -⟩, Hg, ⟨%b1, %b2, %b4, %⟨hb1, hb2, hb4⟩, Z1, Z2, Z4⟩, Hvt, HH⟩
  subst hrs
  mcredits (52 * cfg.regularOpCost + 14 * cfg.regularOpCost + K + R)
  repeat mstep
  -- the `String`
  icases stk_split n out.toNat 4 8 $$ HO with ⟨O0, HO⟩
  icases stk_split n (out.toNat + 4) 4 4 $$ HO with ⟨O4, O8⟩
  iunfold stk at O0 O4 O8
  icases O0 with ⟨%w0, %hw0, O0⟩
  icases O4 with ⟨%w4, %hw4, O4⟩
  icases O8 with ⟨%w8, %hw8, O8⟩
  ihave O8 := memBytes_addr (show out.toNat + 4 + 4 = out.toNat + 8 by omega) $$ O8
  mstep [O8]
  repeat mstep
  mstep [O0]
  repeat mstep
  mstep [O4]
  -- the `Arguments` copied
  ihave Fr := stk_addr (show (s - 32).toNat - 16 + 16 = (s - 32).toNat by omega) $$ Fr
  icases FmtWrite.frame32_open n (s - 32).toNat $$ Fr with ⟨X0, S4, S8, S16, S24⟩
  iunfold stk at S4 S8 S16 S24
  icases S4 with ⟨%v4, %hv4, S4⟩
  icases S8 with ⟨%v8, %hv8, S8⟩
  icases S16 with ⟨%v16, %hv16, S16⟩
  icases S24 with ⟨%v24, %hv24, S24⟩
  ihave L16 := (memBytes_append (GF := GF) (H := NearState) n (ar.toNat + 16) (bytes32 argp) (bytes32 k)).2 $$ [A16 A20]
  · iframe A16; iapply memBytes_addr (show ar.toNat + 20 = ar.toNat + 16 + (bytes32 argp).length by simp [bytes32]) $$ A20
  ihave L8 := (memBytes_append (GF := GF) (H := NearState) n (ar.toNat + 8) (bytes32 0) junk).2 $$ [A8 HJ]
  · iframe A8; iapply memBytes_addr (show ar.toNat + 12 = ar.toNat + 8 + (bytes32 0).length by simp [bytes32]) $$ HJ
  ihave L0 := (memBytes_append (GF := GF) (H := NearState) n ar.toNat (bytes32 pp) (bytes32 k)).2 $$ [A0 A4]
  · iframe A0; iapply memBytes_addr (show ar.toNat + 4 = ar.toNat + (bytes32 pp).length by simp [bytes32]) $$ A4
  repeat mstep
  mstep [S4]
  repeat mstep
  mstep [L16]
  mstep [S24]
  repeat mstep
  mstep [L8]
  mstep [S16]
  repeat mstep
  mstep [L0]
  mstep [S8]
  repeat mstep
  have hb32 : ∀ v : UInt32, (bytes32 v).length = 4 := fun v => by simp [bytes32]
  rw [ResultExpect.bytes64_decode _ (by simp [hb32]), ResultExpect.bytes64_decode _ (by simp [hb32, hjunk]),
    ResultExpect.bytes64_decode _ (by simp [hb32])]
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 32).toNat + 8) (bytes32 pp) (bytes32 k)).1 $$ S8
    with ⟨B0, B4⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 32).toNat + 16) (bytes32 0) junk).1 $$ S16
    with ⟨B8, BJ⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 32).toNat + 24) (bytes32 argp) (bytes32 k)).1 $$ S24
    with ⟨B16, B20⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ar.toNat (bytes32 pp) (bytes32 k)).1 $$ L0
    with ⟨A0, A4⟩
  icases (memBytes_append (GF := GF) (H := NearState) n (ar.toNat + 8) (bytes32 0) junk).1 $$ L8
    with ⟨A8, AJ⟩
  icases (memBytes_append (GF := GF) (H := NearState) n (ar.toNat + 16) (bytes32 argp) (bytes32 k)).1 $$ L16
    with ⟨A16, A20⟩
  simp only [hb32]
  ihave #S872 := hS q hq0 $$ C
  ihave Lo : stk n ((s - 32).toNat - 16) 16 $$ [Z1 Z2 L8 Z4]
  · iapply VecFromElem.stk16_join
    isplitl [Z1]; · iapply FmtU128.stk_of n _ 4 _ hb1 $$ Z1
    isplitl [Z2]
    · iapply FmtU128.stk_of n _ 4 _ hb2
      iapply memBytes_addr (show (s - 32).toNat - 12 = (s - 32).toNat - 16 + 4 by omega) $$ Z2
    iframe L8
    iapply FmtU128.stk_of n _ 4 _ hb4
    iapply memBytes_addr (show (s - 32).toNat - 4 = (s - 32).toNat - 16 + 12 by omega) $$ Z4
  mcall S872 using [Hg B0 B4 B8 B16 B20 S4 Lo HM O0 O4 O8 Hvt HH HP]
  · iframe Hg Lo HM Hvt HH HP
    isplitl [B0 B4 B8 B16 B20]
    · iunfold argsN
      isplitl [B0]; · iapply memBytes_addr (show (s - 32).toNat + 8 = (s - 32 + 8).toNat by omega) $$ B0
      isplitl [B4]; · iapply memBytes_addr (show (s - 32).toNat + 8 + 4 = (s - 32 + 8).toNat + 4 by omega) $$ B4
      isplitl [B8]; · iapply memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 8).toNat + 8 by omega) $$ B8
      isplitl [B16]; · iapply memBytes_addr (show (s - 32).toNat + 24 = (s - 32 + 8).toNat + 16 by omega) $$ B16
      iapply memBytes_addr (show (s - 32).toNat + 24 + 4 = (s - 32 + 8).toNat + 20 by omega) $$ B20
    isplitl [S4]
    · iapply memBytes_addr (show (s - 32).toNat + 4 = (s - 32 + 4).toNat by omega) $$ S4
    iunfold strNew
    iframe O0 O4 O8
  icases HQ with ⟨%hrs, Hg, HA, S4, Lo, HQ⟩
  subst hrs
  repeat mstep
  rw [show s - 32 + 32 = s by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  iframe Hc Hg
  iunfold argsN at HA
  icases HA with ⟨B0, B4, B8, B16, B20⟩
  isplitl [Lo X0 S4 B0 B4 B8 BJ B16 B20]
  · iapply stk_addr (show (s - 32).toNat - 16 = s.toNat - 48 by omega)
    ihave Fr : stk n (s - 32).toNat 32 $$ [X0 S4 B0 B4 B8 BJ B16 B20]
    · iapply FmtWrite.frame32_close n (s - 32).toNat
      iframe X0
      isplitl [S4]
      · iapply stk_word
        iapply memBytes_addr (show (s - 32 + 4).toNat = (s - 32).toNat + 4 by omega) $$ S4
      isplitl [B0 B4]
      · iapply FmtU128.stk_of n _ 8 (bytes32 pp ++ bytes32 k) (by simp [hb32])
        iapply (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 pp) (bytes32 k)).2
        simp only [hb32]
        isplitl [B0]; · iapply memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by omega) $$ B0
        iapply memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 8 + 4 by omega) $$ B4
      isplitl [B8 BJ]
      · iapply FmtU128.stk_of n _ 8 (bytes32 0 ++ junk) (by simp [hb32, hjunk])
        iapply (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 0) junk).2
        simp only [hb32]
        iframe BJ
        iapply memBytes_addr (show (s - 32 + 8).toNat + 8 = (s - 32).toNat + 16 by omega) $$ B8
      iapply FmtU128.stk_of n _ 8 (bytes32 argp ++ bytes32 k) (by simp [hb32])
      iapply (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 argp) (bytes32 k)).2
      simp only [hb32]
      isplitl [B16]; · iapply memBytes_addr (show (s - 32 + 8).toNat + 16 = (s - 32).toNat + 24 by omega) $$ B16
      iapply memBytes_addr (show (s - 32 + 8).toNat + 20 = (s - 32).toNat + 24 + 4 by omega) $$ B20
    ihave Fr := stk_addr (show (s - 32).toNat = (s - 32).toNat - 16 + 16 by omega) $$ Fr
    iapply stk_join n ((s - 32).toNat - 16) 16 32
    iframe Lo Fr
  isplitl [A0 A4 A8 A16 A20]
  · iunfold argsN
    iframe A0 A4 A8 A16
    iapply memBytes_addr (show ar.toNat + 16 + 4 = ar.toNat + 20 by omega) $$ A20
  isplitl [AJ]
  · iapply memBytes_addr (show ar.toNat + 8 + 4 = ar.toNat + 12 by omega) $$ AJ
  iexists q
  iexact HQ

end Spec

end WNear.Binary.FmtFormat
