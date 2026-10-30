import Bridge.Functions.SerdeIgnScalar
import Bridge.Functions.SerdeIgnBudget

/-! # The actual container-opening dispatch of the complete ignored-value reader -/

namespace WNear.Binary.SerdeIgnOpening

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte)
open WNear.Binary.SerdeIgnValue (fr81 ob16 band255)
open WNear.Binary.SerdeIgnMachineStack

/-- The first three actual value-loop blocks: whitespace peek, presence guard, then dispatch. -/
def entryCode : List Instr :=
  SerdeIgnContainer.peekCode 4 ++ SerdeIgnScalar.presentCode ++ SerdeIgnScalar.dispatchBlock

theorem entryCode_at : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).take 3 = entryCode := by rfl

/-- The complete machine selects precisely the saved-frame transition for either opening byte. -/
theorem opening_step (N : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (opened : UInt8) (t : List UInt8) (hopen : Br opened)
    (hskip : NearInterface.Json.skipWhitespace bs = opened :: t)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames bs = some (r, ops)) :
    SerdeIgnMachineTrace.save frames
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.opened opened) frames t) = some (r, ops) := by
  rcases hopen with rfl | rfl <;> simpa only [SerdeIgnMachineTrace.run, hskip] using h

/-- A successful opening supplies the exact consumed-byte cursor and the complete traced save continuation. -/
theorem opening_indices (N : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (i : Nat) (opened : UInt8) (hb : bs[i]? = some opened) (hopen : Br opened)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames
      (bs.drop i) = some (r, ops)) :
    i + 1 ≤ bs.length - r.length ∧ SerdeIgnMachineTrace.save frames
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.opened opened) frames
        (bs.drop (i + 1))) = some (r, ops) := by
  have hi := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hi hb
  have hws : NearInterface.Json.isWhitespace opened = false := by rcases hopen with rfl | rfl <;> rfl
  have hskip : NearInterface.Json.skipWhitespace (bs.drop i) = opened :: bs.drop (i + 1) := by
    rw [hdr, WNear.JsonFuel.skip_of_not _ hws]
  have hs := opening_step N frames (bs.drop i) r ops opened _ hopen hskip h
  obtain ⟨ops', hsub, -⟩ := SerdeIgnSegments.save_some hs
  have hg := SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
    (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N (.opened opened) frames (bs.drop (i + 1))
  have hrest := (hg r ops' hsub).2.1
  simp only [List.length_drop] at hrest
  exact ⟨by omega, hs⟩

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Either actual container byte takes the dispatch through save/eat and out to the opened phase. -/
theorem opening (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 l7 : UInt32)
    (opened : UInt8) (maxP hl F : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8)
    (i : Nat) (Fr : IProp GF) (hopen : Br opened)
    (hs : 80 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hi : i < bs.length)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗
      credits Cg (110 * cfg.regularOpCost + saveCost cfg F cap frames + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (flag frames) l4 (optByte (some opened)) l6 l7 (current fallback frames))
      [] SerdeIgnScalar.valueCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some opened))
            opened.toUInt32 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (i + 1) ∗ Fr) } := by
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hflag : flag frames &&& 1 = flag frames := by cases frames <;> simp only [flag] <;> decide +kernel
  have key := f84_save (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s
    (de + 12) p cap idx fallback maxP hl F live frames opened hs (by rw [hd12]; omega) hcap hframes hr
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd, HF⟩
  iunfold SerdeIgnSegments.code at HC
  icases HC with ⟨#C81, #CR⟩
  iunfold SerdeIgnValue.code81 at C81
  icases C81 with ⟨#CN, -, -, -, -, #F84, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, #F333, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha84 := hm.funcs 84 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  generalize hK : saveCost cfg F cap frames = K at key ⊢
  unfold SerdeIgnScalar.valueCode SerdeIgnScalar.stringBodyCode SerdeIgnScalar.negativeBody
    SerdeIgnScalar.falseBody SerdeIgnScalar.digitBody SerdeIgnSegments.openCode
  simp only [List.cons_append, List.nil_append, fr81]
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [ob16 opened, band255 opened]
  rcases hopen with rfl | rfl
  all_goals
    repeat mstep
    rw [hflag]
    mcall key using [Hg H80 Hvt Hst]
    · iframe Hg H80 Hvt Hst
    icases HQ with ⟨%hrs, %p', %hl', %hh, Hg, H80, Hvt, Hst⟩
    subst hrs
    clear key hK
    repeat mstep
    mcall (SerdeRead.f333_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs i hi hlen
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    repeat mstep
    mcredits R
    iframe Hc
    isplitr
    · ipureintro; trivial
    iexists p', hl'
    iframe Hg H80 Hvt Hst Hrd HF
    ipureintro; exact hh

set_option maxRecDepth 100000 in
/-- The actual enclosing block enters the opened-container phase, including its charged branch exit. -/
theorem opening_block (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 l7 : UInt32)
    (opened : UInt8) (maxP hl F : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8)
    (i : Nat) (Fr : IProp GF) (hopen : Br opened)
    (hs : 80 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hi : i < bs.length)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗
      credits Cg (112 * cfg.regularOpCost + saveCost cfg F cap frames + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (flag frames) l4 (optByte (some opened)) l6 l7 (current fallback frames))
      [] SerdeIgnScalar.dispatchBlock
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some opened))
            opened.toUInt32 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (i + 1) ∗ Fr) } := by
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd, HF⟩
  unfold SerdeIgnScalar.dispatchBlock
  mstep
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hg H80 Hvt Hst Hrd HF]
  · iapply opening cfg lim d inst mi A n g ta hm hd Cg (cfg.regularOpCost + R) gt
      s de ptr p cap idx fallback l4 l6 l7 opened maxP hl F live frames bs i Fr hopen hs hde hcap hlen hi hframes hr
    iframe HC Hg H80 Hvt Hst Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, %p', %hl', %hh, Hg, H80, Hvt, Hst, Hrd, HF⟩
    subst hk; subst hvs; subst hfr
    simp only [Post.mseq, Post.mblock_br_zero, List.length_nil, List.drop_nil, List.nil_append]
    isplitr
    · ipureintro; omega
    mpay
    iframe Hc
    isplitr
    · ipureintro; trivial
    iexists p', hl'
    iframe Hg H80 Hvt Hst Hrd HF
    ipureintro; exact hh
  isplit
  · iintro %vs %fr H; simp only [Post.mseq_ret, Post.mblock_ret]; iexact H
  · iintro H; simp only [Post.mseq_trap, Post.mblock_trap]; iexact H

set_option maxRecDepth 100000 in
/-- The complete opening dispatch and block preserve the traced continuation and charge the actual save prefix. -/
theorem opening_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 l7 : UInt32)
    (opened : UInt8) (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i : Nat) (Fr : IProp GF) (hopen : Br opened) (hs : 80 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hi : i < bs.length)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1)
    (hmodel : SerdeIgnMachineTrace.save frames
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.opened opened) frames (bs.drop (i + 1))) = some (r, ops)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗
      credits Cg (252 * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d
      (fr81 inst mi de s (flag frames) l4 (optByte (some opened)) l6 l7 (current fallback frames))
      [] SerdeIgnScalar.dispatchBlock
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = saveOps frames ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.opened opened) frames (bs.drop (i + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some opened)) opened.toUInt32 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (i + 1) ∗ Fr) } := by
  obtain ⟨ops', hsub, hops⟩ := SerdeIgnSegments.save_some hmodel
  have hsave := saveCost_le cfg F cap frames
  have hcost : 112 * cfg.regularOpCost + saveCost cfg F cap frames +
      (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' + R) ≤
      252 * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R := by
    rw [hops, save_extraCost]
    omega
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H80 Hvt Hst Hrd HF]
  · iapply opening_block cfg lim d inst mi A n g ta hm hd Cg
      (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' + R)
      gt s de ptr p cap idx fallback l4 l6 l7 opened maxP hl F live frames bs i Fr hopen hs hde hcap hlen hi hframes hr
    iframe HC Hg H80 Hvt Hst Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H
    iexists ops'
    isplitr
    · ipureintro; exact ⟨hops, hsub⟩
    iexact H
  isplit
  · iintro %k %vs %fr H; iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

set_option maxRecDepth 100000 in
/-- The complete actual value-entry prefix opens a container after whitespace and preserves its trace. -/
theorem entry (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 l7 : UInt32) (l5 : UInt64)
    (opened : UInt8) (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i q : Nat) (Fr : IProp GF) (hopen : Br opened) (hs : 80 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + SerdeRead.wsLen (bs.drop i)) (hb : bs[q]? = some opened)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1)
    (hmodel : SerdeIgnMachineTrace.save frames
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.opened opened) frames (bs.drop (q + 1))) = some (r, ops)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗
      credits Cg ((384 + 96 * SerdeRead.wsLen (bs.drop i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d
      (fr81 inst mi de s (flag frames) l4 l5 l6 l7 (current fallback frames)) [] entryCode
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = saveOps frames ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.opened opened) frames (bs.drop (q + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some opened)) opened.toUInt32 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd, HF⟩
  ihave #HC' := HC
  iunfold SerdeIgnSegments.code at HC'
  icases HC' with ⟨#C81, -⟩
  unfold entryCode
  rw [List.append_assoc]
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hg H80 Hvt Hst Hrd HF]
  · iapply SerdeIgnContainer.peek_success cfg lim d inst mi A n g ta hm (by omega) Cg
      (259 * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R)
      4 de s ptr (flag frames) l4 l6 l7 (current fallback frames) l5 bs i
      (iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ Fr))
      hi hlen hptr (by omega)
    iframe C81 Hrd Hg H80 Hvt Hst HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hrd, Hg, H80, Hvt, Hst, HF⟩
    rw [← hq, hb] at hfr
    subst hvs; subst hfr
    rw [← hq]
    simp only [Post.mseq_normal]
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc Hg H80 Hvt Hst Hrd HF]
    · iapply SerdeIgnScalar.present cfg lim d inst mi Cg
        (252 * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R)
        de s (flag frames) l4 l6 l7 (current fallback frames) opened
        (iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs q ∗ Fr))
      iframe Hg H80 Hvt Hst Hrd HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    isplit
    · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hg, H80, Hvt, Hst, Hrd, HF⟩
      subst hvs; subst hfr
      simp only [Post.mseq_normal]
      iapply opening_traced cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap idx fallback l4 l6 l7
        opened maxP hl F N live frames bs r ops q Fr hopen hs hde hcap hlen hq_lt hframes hr hmodel
      iframe HC Hc Hg H80 Hvt Hst Hrd HF
    isplit
    · iintro %k %vs %fr H; simp only [Post.mseq]; iexact H
    isplit
    · iintro %vs %fr H; simp only [Post.mseq_ret]; iexact H
    · iintro H; simp only [Post.mseq_trap]; iexact H
  isplit
  · iintro %k %vs %fr H; simp only [Post.mseq]; iexact H
  isplit
  · iintro %vs %fr H; simp only [Post.mseq_ret]; iexact H
  · iintro H; simp only [Post.mseq_trap]; iexact H

set_option maxRecDepth 100000 in
/-- The complete opening prefix establishes the opened-phase reserve under the unchanged per-byte charge.
Six operations remain available for surrounding loop control; allocation growth is charged by the actual trace. -/
theorem entry_funded (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 l7 : UInt32) (l5 : UInt64)
    (opened : UInt8) (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i q : Nat) (Fr : IProp GF) (hopen : Br opened) (hs : 80 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + SerdeRead.wsLen (bs.drop i)) (hb : bs[q]? = some opened)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames
      (bs.drop i) = some (r, ops)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnBudget.regular cfg (if frames.length = 0 then 109 else 60)
          (bs.length - r.length - i) frames.length + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d
      (fr81 inst mi de s (flag frames) l4 l5 l6 l7 (current fallback frames)) [] entryCode
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = saveOps frames ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.opened opened) frames (bs.drop (q + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' +
            (6 * cfg.regularOpCost + SerdeIgnBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
              (bs.length - r.length - (q + 1)) (frames.length + 1) + R)) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some opened)) opened.toUInt32 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hq_lt hb
  have hskip : NearInterface.Json.skipWhitespace (bs.drop i) = opened :: bs.drop (q + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop, ← hq, hdr]
  have hsave := opening_step N frames (bs.drop i) r ops opened _ hopen hskip hmodel
  obtain ⟨ops', hsub, -⟩ := SerdeIgnSegments.save_some hsave
  have hdepth : frames.length + 1 ≤ bs.length - r.length - (q + 1) := by
    simpa only [SerdeIgnBudget.active] using
      SerdeIgnBudget.active_le_remaining N (.opened opened) frames bs r ops' (q + 1) hsub
  have hsplit : bs.length - r.length - i =
      SerdeRead.wsLen (bs.drop i) + 1 + (bs.length - r.length - (q + 1)) := by omega
  have hcharge := SerdeIgnBudget.opening_cost cfg opened (SerdeRead.wsLen (bs.drop i))
    (bs.length - r.length - (q + 1)) frames.length hdepth
  have hcost : (384 + 96 * SerdeRead.wsLen (bs.drop i)) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops +
      (6 * cfg.regularOpCost + SerdeIgnBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
        (bs.length - r.length - (q + 1)) (frames.length + 1) + R) ≤
      SerdeIgnBudget.regular cfg (if frames.length = 0 then 109 else 60)
        (bs.length - r.length - i) frames.length +
        SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R := by
    rw [hsplit]
    simp only [Nat.add_mul] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd, HF⟩
  iapply entry cfg lim d inst mi A n g ta hm hd Cg
    (6 * cfg.regularOpCost + SerdeIgnBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
      (bs.length - r.length - (q + 1)) (frames.length + 1) + R)
    gt s de ptr p cap idx fallback l4 l6 l7 l5 opened maxP hl F N live frames bs r ops i q Fr
    hopen hs hde hcap hlen hptr hi hq hb hframes hr hsave
  iframe HC Hg H80 Hvt Hst Hrd HF
  iapply BorrowMut.credits_le
  iframe Hc
  ipureintro; exact hcost

end Proof
end WNear.Binary.SerdeIgnOpening
