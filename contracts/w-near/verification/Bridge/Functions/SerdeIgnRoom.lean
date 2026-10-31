import Bridge.Functions.SerdeIgnExecution

namespace WNear.Binary.SerdeIgnExecution
open Wasm Wasm.Near

/-- Total requested pages suffice even when every reserve grows the heap. -/
theorem room_of_pages (maxP hl : Nat) (cap : UInt32) (len : Nat) (ops : List SerdeIgnTrace.Op)
    (hmax : maxP ≤ 65535) (hpos : 0 < hl) (halign : hl % 65536 = 0)
    (hpages : hl + 65536 * SerdeIgnTrace.pages cap len ops ≤ maxP * 65536) :
    Room maxP hl cap len ops := by
  induction ops generalizing hl cap len with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | false =>
      simp only [SerdeIgnTrace.pages, SerdeIgnTrace.grows, Bool.false_and, Bool.false_eq_true,
        ite_false, Nat.zero_add, SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen] at hpages
      exact ih hl cap (len - 1) hpos halign hpages
    | true =>
      by_cases hf : ScratchGrow.fits cap (UInt32.ofNat len) 1
      · simp only [SerdeIgnTrace.pages, SerdeIgnTrace.grows, Bool.true_and, hf, not_true_eq_false,
          decide_false, Bool.false_eq_true, ite_false, Nat.zero_add, SerdeIgnTrace.nextCap,
          SerdeIgnTrace.nextLen, ScratchGrow.capAfter, if_pos hf] at hpages
        constructor
        · exact fun hn => False.elim (hn hf)
        · intro hl' hh
          simp only [ScratchGrow.hlAfter, if_pos hf] at hh
          subst hl'
          simpa only [SerdeIgnTrace.nextCap, ite_true, ScratchGrow.capAfter, if_pos hf] using
            ih hl cap (len + 1) hpos halign hpages
      · simp only [SerdeIgnTrace.pages, SerdeIgnTrace.grows, Bool.true_and, hf, not_false_eq_true,
          decide_true, ite_true, SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen,
          ScratchGrow.capAfter, if_neg hf] at hpages
        let size := VecGrow.growCap cap (UInt32.ofNat len + 1)
        let pages := (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat
        change hl + 65536 * (pages + SerdeIgnTrace.pages size (len + 1) ops) ≤ maxP * 65536 at hpages
        have hroom : VecFromElem.roomFor hl maxP size := by
          unfold VecFromElem.roomFor
          change hl % 65536 = 0 ∧ 0 < hl ∧ hl + pages * 65536 + 65536 ≤ 2 ^ 32 ∧
            (hl + pages * 65536) / 65536 ≤ maxP
          simp only [Nat.mul_add] at hpages
          exact ⟨halign, hpos, by omega, by omega⟩
        constructor
        · exact fun _ => hroom
        · intro hl' hh
          simp only [SerdeIgnTrace.nextCap, ite_true, ScratchGrow.capAfter, if_neg hf]
          simp only [ScratchGrow.hlAfter, if_neg hf] at hh
          rcases hh with he | he
          · subst hl'
            apply ih hl size (len + 1) hpos halign
            simp only [Nat.mul_add] at hpages
            omega
          · subst hl'
            change Room maxP (hl + pages * 65536) size (len + 1) ops
            apply ih (hl + pages * 65536) size (len + 1) (by omega)
            · simpa [Nat.add_mod, Nat.mul_mod] using halign
            · simp only [Nat.mul_add] at hpages
              omega
/-- The exact successful allocation history preserves alignment and spends no more than the requested pages. -/
theorem heap_pages_bound (hl : Nat) (cap : UInt32) (len : Nat) (ops : List SerdeIgnTrace.Op) (final : Nat)
    (ht : HeapTrace hl cap len ops final) :
    hl ≤ final ∧ final ≤ hl + 65536 * SerdeIgnTrace.pages cap len ops ∧
      final % 65536 = hl % 65536 := by
  induction ops generalizing hl cap len with
  | nil =>
    have he : final = hl := ht
    subst final
    simp [SerdeIgnTrace.pages]
  | cons op ops ih =>
    cases op with
    | false =>
      have hh := ih hl cap (len - 1) ht
      simpa [SerdeIgnTrace.pages, SerdeIgnTrace.grows, SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen] using hh
    | true =>
      obtain ⟨hl', hh, ht⟩ := ht
      have hr := ih hl' (SerdeIgnTrace.nextCap cap len true) (len + 1) ht
      by_cases hf : ScratchGrow.fits cap (UInt32.ofNat len) 1
      · simp only [ScratchGrow.hlAfter, if_pos hf] at hh
        subst hl'
        simpa only [SerdeIgnTrace.pages, SerdeIgnTrace.grows, Bool.true_and, hf, not_true_eq_false,
          decide_false, Bool.false_eq_true, ite_false, Nat.zero_add, SerdeIgnTrace.nextLen, ite_true] using hr
      · simp only [ScratchGrow.hlAfter, if_neg hf] at hh
        simp only [SerdeIgnTrace.pages, SerdeIgnTrace.grows, Bool.true_and, hf, not_false_eq_true,
          decide_true, ite_true, SerdeIgnTrace.nextLen]
        simp only [SerdeIgnTrace.nextCap, ite_true, ScratchGrow.capAfter, if_neg hf] at hr ⊢
        rcases hh with he | he
        · subst hl'
          exact ⟨hr.1, by simp only [Nat.mul_add]; omega, hr.2.2⟩
        · subst hl'
          simp only [VecFromElem.grownLen] at hr
          refine ⟨by omega, ?_, ?_⟩
          · simp only [Nat.mul_add]
            omega
          · simpa [Nat.add_mod, Nat.mul_mod] using hr.2.2

/-- A successful bounded value preserves the object caller's strict capacity bound. -/
theorem trace_end_cap_v86 (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (cap : UInt32)
    (hlen : bs.length ≤ 4194304) (hcap : cap.toNat < 2 ^ 25)
    (htrace : SerdeIgnMachineTrace.trace bs = some (r, ops)) :
    (SerdeIgnTrace.endState cap 0 ops).1.toNat < 2 ^ 25 := by
  have hskip : WNear.IgnoreModel.vSkip bs = some r := by
    rw [← SerdeIgnMachineTrace.erase_trace, htrace]
    rfl
  obtain ⟨os, ht, hv, _, _, hp⟩ := SerdeIgnMachineTrace.trace_valid cap (by omega) (by omega) hskip
  have he : ops = os := (Prod.mk.inj (Option.some.inj (htrace.symm.trans ht))).2
  subst os
  have hc := SerdeIgnTrace.endState_capacity cap 0 ops hv
  omega

/-- Concrete page reserve for a successful value on the pinned argument-size domain. -/
theorem trace_pages_v86 (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (cap : UInt32)
    (hlen : bs.length ≤ 4194304) (hcap : cap.toNat < 2 ^ 27)
    (htrace : SerdeIgnMachineTrace.trace bs = some (r, ops)) :
    65536 * SerdeIgnTrace.pages cap 0 ops ≤ 18362816 := by
  have hskip : WNear.IgnoreModel.vSkip bs = some r := by
    rw [← SerdeIgnMachineTrace.erase_trace, htrace]
    rfl
  obtain ⟨os, ht, hv, _, _, hp⟩ := SerdeIgnMachineTrace.trace_valid cap hcap (by omega) hskip
  have he : ops = os := (Prod.mk.inj (Option.some.inj (htrace.symm.trans ht))).2
  subst os
  have hc := SerdeIgnTrace.endState_capacity cap 0 ops hv
  have hfinal : (SerdeIgnTrace.endState cap 0 ops).1.toNat < 2 ^ 27 := by omega
  have hg : SerdeIgnTrace.growthCount cap 0 ops ≤ 24 := by
    by_contra hn
    have hpower := SerdeIgnTrace.growthCount_power cap 0 ops hv (by omega)
    have he : 24 ≤ SerdeIgnTrace.growthCount cap 0 ops - 1 := by omega
    have hpow := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_right (n := 2) (by decide) he)
    change 134217728 ≤ 8 * 2 ^ (SerdeIgnTrace.growthCount cap 0 ops - 1) at hpow
    omega
  have ha := SerdeIgnTrace.allocatedBytes_peak cap 0 ops hv
  have hpages := SerdeIgnTrace.pages_scaled cap 0 ops hv
  omega

/-- A concrete 96 MiB reachable heap has enough room for every frame growth of one 4 MiB value. -/
theorem room_v86 (hl : Nat) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (cap : UInt32)
    (hlen : bs.length ≤ 4194304) (hcap : cap.toNat < 2 ^ 27)
    (htrace : SerdeIgnMachineTrace.trace bs = some (r, ops))
    (hpos : 0 < hl) (halign : hl % 65536 = 0) (hheap : hl ≤ 100663296) :
    Room 2048 hl cap 0 ops := by
  apply room_of_pages 2048 hl cap 0 ops (by decide) hpos halign
  have hp := trace_pages_v86 bs r ops cap hlen hcap htrace
  omega

open WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
section
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem f81_traced_of_pages (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr p cap idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (sl : UInt32) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (i : Nat) (Fr : IProp GF)
    (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hcap : cap.toNat < 2 ^ 27)
    (htrace : SerdeIgnMachineTrace.trace (bs.drop i) = some (r, ops))
    (hmax : maxP ≤ 65535) (hpos : 0 < hl) (halign : hl % 65536 = 0)
    (hpages : hl + 65536 * SerdeIgnTrace.pages cap 0 ops ≤ maxP * 65536) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ⊢ MFunSpec cfg lim d type inst mi f81 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeValueState.scratchPre n maxP hl live F de p cap sl ∗ rd n de ptr bs i ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      (fun _ => (166 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops)
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
  exact f81_traced cfg lim d type htype inst mi A n g ta hm hd Cg gt sp de ptr p cap idx maxP hl F live sl bs r ops i Fr
    hsp hde hlen hptr hi hcap htrace (room_of_pages maxP hl cap 0 ops hmax hpos halign hpages)

theorem f81_traced_v86 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr p cap idx : UInt32) (hl F : Nat) (live : List (Nat × Nat))
    (sl : UInt32) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (i : Nat) (Fr : IProp GF)
    (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hcap : cap.toNat < 2 ^ 27)
    (htrace : SerdeIgnMachineTrace.trace (bs.drop i) = some (r, ops))
    (hpos : 0 < hl) (halign : hl % 65536 = 0) (hheap : hl ≤ 100663296) :
    SerdeIgnMember.code (GF := GF) n 2048 inst mi A ⊢ MFunSpec cfg lim d type inst mi f81 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeValueState.scratchPre n 2048 hl live F de p cap sl ∗ rd n de ptr bs i ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      (fun _ => (166 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops)
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n 2048 hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
  apply f81_traced_of_pages cfg lim d type htype inst mi A n g ta hm hd Cg gt sp de ptr p cap idx 2048 hl F live sl bs r ops i Fr
    hsp hde (by omega) hptr hi hcap htrace (by decide) hpos halign
  have hp := trace_pages_v86 (bs.drop i) r ops cap (by simp only [List.length_drop]; omega) hcap htrace
  omega

theorem f201_traced_v86 (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp acc de ptr p cap sl idx : UInt32)
    (hl F : Nat) (live : List (Nat × Nat)) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (i : Nat) (Fr : IProp GF)
    (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32) (hacc : acc.toNat + 4 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hi : i ≤ bs.length)
    (hc : bs[i + wsLen (bs.drop i)]? = some 0x3A) (hcap : cap.toNat < 2 ^ 27)
    (htrace : SerdeIgnMachineTrace.trace (bs.drop (i + wsLen (bs.drop i) + 1)) = some (r, ops))
    (hpos : 0 < hl) (halign : hl % 65536 = 0) (hheap : hl ≤ 100663296) :
    SerdeEnds.endCode n 2048 inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code (GF := GF) n 2048 inst mi A ⊢
    MFunSpec cfg lim d types[32]! inst mi f201 Cg
      (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeValueState.scratchPre n 2048 hl live F de p cap sl ∗ rd n de ptr bs i ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      (fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
        ((166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
          SerdeIgnTrace.extraCost cfg F cap 0 ops))
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        n ↦[i32][ acc.toNat ] de ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
        AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n 2048 hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
  have hcolon := SerdeNextKey.getElem_lt hc
  have key89 := SerdeColonSuccess.f89_colon (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp de ptr bs i (by omega) (by omega) (by omega) hi hc
  have key81 := f81_traced_v86 (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp de ptr p cap idx hl F live sl bs r ops (i + wsLen (bs.drop i) + 1) Fr
    hsp hde hlen (by omega) (by omega) hcap htrace hpos halign hheap
  iintro ⟨#Hend, #F89, #F81, #HC⟩
  ihave #Hend' := Hend
  iunfold SerdeEnds.endCode at Hend'
  icases Hend' with ⟨#Herror, -, -, #F332, #F333, #F339⟩
  iunfold SerdeErrBox.errCode at Herror
  icases Herror with ⟨#H310, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310
    icases H310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha89 := hm.funcs 89 (by decide)
  have ha81 := hm.funcs 81 (by decide)
  have t32 : types[32]!.params.length = 1 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hacc, Hg, H160, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
  subst args
  simp only [f201]
  rw [show (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost =
    40 * cfg.regularOpCost + (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost by simp only [Nat.add_mul]; omega]
  generalize hK : (166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
    SerdeIgnTrace.extraCost cfg F cap 0 ops = K at key81 ⊢
  generalize hE : (200 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost = E at key89 ⊢
  ihave #S81 := key81 $$ HC
  mstep; mstep; mstep [Hacc]
  mcall key89 using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  mstep
  mstep_not_taken with decide
  mstep; mstep [Hacc]
  mcall S81 using [Hg H160 Hvt Hst Hrd He Hhex Hid HF]
  · iframe Hg H160 Hvt Hst Hrd He Hhex Hid HF
  icases HQ with ⟨%p', %hl', %⟨hrs, hheap⟩, Hg, H160, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
  subst hrs
  mstep
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists p', hl'
  iframe Hacc Hg H160 Hvt Hst Hrd He Hhex Hid HF
  ipureintro; exact ⟨rfl, hheap⟩


end
end WNear.Binary.SerdeIgnExecution
