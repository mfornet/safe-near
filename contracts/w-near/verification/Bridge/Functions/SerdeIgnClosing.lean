import Bridge.Functions.SerdeIgnOpening

/-! # Complete closing iterations of the actual ignored-container loop -/

namespace WNear.Binary.SerdeIgnClosing

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnContainer (closing)

/-- The real closing/member dispatch block, including the branch back to the loop. -/
def blockCode : List Instr :=
  [.block .empty (SerdeIgnContainer.dispatchCode ++ SerdeIgnSegments.closeCode ++ [.br 1])]

theorem blockCode_at : ((SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 3, 0]).drop 1).take 1 =
    blockCode := by rfl

/-- The whole actual container-loop body consists of its peek and closing/member block. -/
def iterationCode : List Instr := SerdeIgnContainer.peekCode 6 ++ blockCode

theorem iterationCode_at : SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 3, 0] = iterationCode := by rfl

/-- A matching close selects the same pop continuation in either complete container phase. -/
theorem close_step (N : Nat) (opened : Bool) (current : UInt8) (frames bs t r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (hcurrent : Br current)
    (hskip : NearInterface.Json.skipWhitespace bs = closing current :: t)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) frames bs = some (r, ops)) :
    SerdeIgnMachineTrace.pop true frames t
      (fun f frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont f) frames t) =
        some (r, ops) := by
  rcases SerdeIgnContainer.phase_cases N opened current (closing current) frames bs t r ops hcurrent hskip h with
    ⟨-, hp⟩ | ⟨-, h93, h125, -⟩ | ⟨-, heq, -⟩
  · exact hp
  · rcases hcurrent with rfl | rfl
    · exact (h93 rfl).elim
    · exact (h125 rfl).elim
  · rcases hcurrent with rfl | rfl <;> simp [closing] at heq

/-- Full-machine success supplies the matching close cursor and its exact saved-frame continuation. -/
theorem close_indices (N : Nat) (opened : Bool) (current : UInt8) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i q : Nat) (hcurrent : Br current)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current))
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) frames (bs.drop i) = some (r, ops)) :
    q + 1 ≤ bs.length - r.length ∧ SerdeIgnMachineTrace.pop true frames (bs.drop (q + 1))
      (fun f frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont f) frames t) =
        some (r, ops) := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hq_lt hb
  have hskip : NearInterface.Json.skipWhitespace (bs.drop i) = closing current :: bs.drop (q + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop, ← hq, hdr]
  have hp := close_step N opened current frames (bs.drop i) _ r ops hcurrent hskip h
  have hg := SerdeIgnMachineTrace.good_pop true frames (bs.drop (q + 1))
    (fun f frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont f) frames t)
    (fun f frames t => SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
      (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N (.cont f) frames t)
  have hrest := (hg r ops hp).2.1
  simp only [List.length_drop] at hrest
  exact ⟨by omega, hp⟩

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- A matching close with a saved head restores that head and branches back to the container loop. -/
theorem block_nonempty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current saved : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8) (i : Nat) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hi : i < bs.length) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (212 * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (saved :: frames) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 (optByte (some (closing current))) l6 l7 current.toUInt32) [] blockCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 l4 (optByte (some (closing current)))
            (closing current).toUInt32 l7 saved.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗
          rd n de ptr bs (i + 1) ∗ Fr) } := by
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  unfold blockCode
  rw [List.append_assoc]
  mstep
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply SerdeIgnContainer.dispatch_close cfg lim d inst mi Cg (111 * cfg.regularOpCost + R)
      de s l3 l4 l6 l7 current hcurrent
      (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (saved :: frames) ∗
        rd n de ptr bs i ∗ Fr))
    iframe H32 Hst Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, H32, Hst, Hrd, HF⟩
    subst hvs; subst hfr
    simp only [Post.mseq_normal]
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc H32 Hst Hrd HF]
    · iapply mwpi_frame (R := Fr)
      isplitl [HF]
      · iexact HF
      iapply SerdeIgnSegments.close_nonempty cfg lim d inst mi A n g ta hm hd Cg (cfg.regularOpCost + R)
        s de ptr p cap l3 l4 (closing current).toUInt32 l7 current.toUInt32 (optByte (some (closing current)))
        saved maxP hl F live frames bs i hs hde hlen hi
      iframe HC H32 Hst Hrd
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    simp only [Post.frame]
    isplit
    · iintro %vs %fr ⟨HF, Hc, %⟨hvs, hfr⟩, H32, Hst, Hrd⟩
      subst hvs; subst hfr
      simp only [Post.mseq_normal]
      mstep
      mcredits R
      iframe Hc H32 Hst Hrd HF
      ipureintro; trivial
    isplit
    · iintro %k %vs %fr ⟨-, H⟩; iexfalso; iexact H
    isplit
    · iintro %vs %fr ⟨-, H⟩; iexfalso; iexact H
    · iintro ⟨-, H⟩; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- Closing the last container takes the actual success exit, retaining the cleared vector allocation. -/
theorem block_empty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i : Nat) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hi : i < bs.length) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (211 * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 (optByte (some (closing current))) l6 l7 current.toUInt32) [] blockCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 4 ∧ vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some (closing current)))
            (closing current).toUInt32 l7 current.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
          rd n de ptr bs (i + 1) ∗ Fr) } := by
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  unfold blockCode
  rw [List.append_assoc]
  mstep
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply SerdeIgnContainer.dispatch_close cfg lim d inst mi Cg (110 * cfg.regularOpCost + R)
      de s l3 l4 l6 l7 current hcurrent
      (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
        rd n de ptr bs i ∗ Fr))
    iframe H32 Hst Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, H32, Hst, Hrd, HF⟩
    subst hvs; subst hfr
    simp only [Post.mseq_normal]
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc H32 Hst Hrd HF]
    · iapply mwpi_frame (R := Fr)
      isplitl [HF]
      · iexact HF
      iapply SerdeIgnSegments.close_empty cfg lim d inst mi A n g ta hm hd Cg R
        s de ptr p cap l3 l4 (closing current).toUInt32 l7 current.toUInt32 (optByte (some (closing current)))
        maxP hl F live bs i hs hde hlen hi
      iframe HC H32 Hst Hrd
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    simp only [Post.frame]
    isplit
    · iintro %vs %fr ⟨-, H⟩; iexfalso; iexact H
    isplit
    · iintro %k %vs %fr ⟨HF, Hc, %⟨hk, hvs, hfr⟩, H32, Hst, Hrd⟩
      subst hk; subst hvs; subst hfr
      simp only [Post.mseq_br, Post.mblock_br_succ, List.nil_append]
      iframe Hc H32 Hst Hrd HF
      ipureintro; trivial
    isplit
    · iintro %vs %fr ⟨-, H⟩; iexfalso; iexact H
    · iintro ⟨-, H⟩; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- The complete actual closing iteration, including its whitespace peek. -/
theorem iteration_nonempty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current saved : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8) (i q : Nat) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg ((337 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (saved :: frames) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 current.toUInt32) [] iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 l4 (optByte (some (closing current)))
            (closing current).toUInt32 l7 saved.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗
          rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  ihave #HC' := HC
  iunfold SerdeIgnSegments.code at HC'
  icases HC' with ⟨#C81, -⟩
  unfold iterationCode
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply SerdeIgnContainer.peek_success cfg lim d inst mi A n g ta hm hd Cg
      (212 * cfg.regularOpCost + R) 6 de s ptr l3 l4 l6 l7 current.toUInt32 l5 bs i
      (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (saved :: frames) ∗ Fr))
      hi hlen hptr (by omega)
    iframe C81 Hrd H32 Hst HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hrd, H32, Hst, HF⟩
    rw [← hq, hb] at hfr
    subst hvs; subst hfr
    rw [← hq]
    simp only [Post.mseq_normal]
    iapply block_nonempty cfg lim d inst mi A n g ta hm (by omega) Cg R
      s de ptr p cap l3 l4 l6 l7 current saved hcurrent maxP hl F live frames bs q Fr hs hde hlen hq_lt
    iframe HC Hc H32 Hst Hrd HF
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- The complete actual closing iteration, including its whitespace peek. -/
theorem iteration_empty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i q : Nat) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg ((336 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 current.toUInt32) [] iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 4 ∧ vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some (closing current)))
            (closing current).toUInt32 l7 current.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
          rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  ihave #HC' := HC
  iunfold SerdeIgnSegments.code at HC'
  icases HC' with ⟨#C81, -⟩
  unfold iterationCode
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply SerdeIgnContainer.peek_success cfg lim d inst mi A n g ta hm hd Cg
      (211 * cfg.regularOpCost + R) 6 de s ptr l3 l4 l6 l7 current.toUInt32 l5 bs i
      (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗ Fr))
      hi hlen hptr (by omega)
    iframe C81 Hrd H32 Hst HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hrd, H32, Hst, HF⟩
    rw [← hq, hb] at hfr
    subst hvs; subst hfr
    rw [← hq]
    simp only [Post.mseq_normal]
    iapply block_empty cfg lim d inst mi A n g ta hm (by omega) Cg R
      s de ptr p cap l3 l4 l6 l7 current hcurrent maxP hl F live bs q Fr hs hde hlen hq_lt
    iframe HC Hc H32 Hst Hrd HF
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- A complete matching-close iteration releases the closed frame reserve and retains the outer continuation. -/
theorem funded_nonempty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current saved : UInt8) (hcurrent : Br current)
    (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8) (i q : Nat) (opened : Bool) (ops : List SerdeIgnTrace.Op) (r : List UInt8) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current))
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) (saved :: frames) (bs.drop i) = some (r, ops)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 2) +
        SerdeIgnTrace.extraCost cfg F cap (saved :: frames).length ops + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (saved :: frames) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 current.toUInt32) [] iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ ops',
          ⌜ops = false :: ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.cont saved) frames (bs.drop (q + 1)) = some (r, ops')⌝ ∗
          credits Cg (18 * cfg.regularOpCost +
            SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops' + R) ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 l4 (optByte (some (closing current)))
            (closing current).toUInt32 l7 saved.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗
          rd n de ptr bs (q + 1) ∗ Fr) } := by
  obtain ⟨hqQ, hpop⟩ := close_indices N opened current (saved :: frames) bs r ops i q hcurrent hq hb hmodel
  obtain ⟨ops', hsub, hops⟩ := SerdeIgnSegments.restore_some hpop
  have hdepth : frames.length + 1 ≤ bs.length - r.length - (q + 1) := by
    simpa only [SerdeIgnBudget.active] using
      SerdeIgnBudget.active_le_remaining N (.cont saved) frames bs r ops' (q + 1) hsub
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + 1 + (bs.length - r.length - (q + 1)) := by omega
  have hcharge := SerdeIgnBudget.closing_cost cfg (wsLen (bs.drop i))
    (bs.length - r.length - (q + 1)) (frames.length + 1) hdepth
  have hextra : SerdeIgnTrace.extraCost cfg F cap (saved :: frames).length ops =
      SerdeIgnTrace.extraCost cfg F cap frames.length ops' := by
    rw [hops, SerdeIgnMachineStack.pop_extraCost]
  have hcost : (337 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
      (18 * cfg.regularOpCost + SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q + 1))
        (frames.length + 1) + SerdeIgnTrace.extraCost cfg F cap frames.length ops' + R) ≤
      SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 2) +
        SerdeIgnTrace.extraCost cfg F cap (saved :: frames).length ops + R := by
    rw [hextra, hsplit]
    simp only [Nat.add_mul, Nat.add_assoc, Nat.reduceAdd] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply iteration_nonempty cfg lim d inst mi A n g ta hm hd Cg
      (18 * cfg.regularOpCost + SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q + 1))
        (frames.length + 1) + SerdeIgnTrace.extraCost cfg F cap frames.length ops' + R)
      s de ptr p cap l3 l4 l6 l7 current saved hcurrent maxP hl F live frames bs i q l5 Fr
      hs hde hlen hptr hi hq hb
    iframe HC H32 Hst Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexact H
  isplit
  · iintro %k %vs %fr H
    iexists ops'
    isplitr
    · ipureintro; exact ⟨hops, hsub⟩
    iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

set_option maxRecDepth 100000 in
/-- The final complete closing iteration spends the last depth reserve and retains credits for success cleanup. -/
theorem funded_empty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current : UInt8) (hcurrent : Br current)
    (maxP hl F N : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i q : Nat) (opened : Bool) (ops : List SerdeIgnTrace.Op) (r : List UInt8) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current))
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) [] (bs.drop i) = some (r, ops)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) 1 +
        SerdeIgnTrace.extraCost cfg F cap 0 ops + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 current.toUInt32) [] iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(⌜ops = [] ∧ r = bs.drop (q + 1) ∧ bs.length - r.length = q + 1⌝ ∗
          credits Cg (19 * cfg.regularOpCost + R) ∗
          ⌜k = 4 ∧ vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some (closing current)))
            (closing current).toUInt32 l7 current.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
          rd n de ptr bs (q + 1) ∗ Fr) } := by
  obtain ⟨hqQ, hpop⟩ := close_indices N opened current [] bs r ops i q hcurrent hq hb hmodel
  simp only [SerdeIgnMachineTrace.pop, Option.some.injEq, Prod.mk.injEq] at hpop
  obtain ⟨hr, hops⟩ := hpop
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hrlen := congrArg List.length hr
  simp only [List.length_drop] at hrlen
  have hend : bs.length - r.length = q + 1 := by omega
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + 1 := by omega
  have hextra : SerdeIgnTrace.extraCost cfg F cap 0 ops = 0 := by rw [← hops]; rfl
  have hz : SerdeIgnBudget.regular cfg 0 0 0 = 0 := by simp [SerdeIgnBudget.regular]
  have hcharge := SerdeIgnBudget.closing_cost cfg (wsLen (bs.drop i)) 0 0 (by omega)
  rw [hz] at hcharge
  simp only [Nat.add_zero, Nat.zero_add] at hcharge
  have hcost : (336 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + (19 * cfg.regularOpCost + R) ≤
      SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) 1 +
        SerdeIgnTrace.extraCost cfg F cap 0 ops + R := by
    rw [hextra, hsplit]
    simp only [Nat.add_mul] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply iteration_empty cfg lim d inst mi A n g ta hm hd Cg (19 * cfg.regularOpCost + R)
      s de ptr p cap l3 l4 l6 l7 current hcurrent maxP hl F live bs i q l5 Fr hs hde hlen hptr hi hq hb
    iframe HC H32 Hst Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexact H
  isplit
  · iintro %k %vs %fr H
    isplitr
    · ipureintro; exact ⟨hops.symm, hr.symm, hend⟩
    iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

set_option maxRecDepth 100000 in
/-- The entire actual container iteration selects the first member, preserving caller resources. -/
theorem iteration_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l4 l6 l7 l8 : UInt32) (l5 : UInt64) (c : UInt8) (bs : List UInt8) (i q : Nat)
    (Fr : IProp GF) (h93 : c ≠ 0x5D) (h125 : c ≠ 0x7D) (h44 : c ≠ 0x2C) (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some c) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ credits Cg ((162 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 0 l4 l5 l6 l7 l8) [] iterationCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some c)) c.toUInt32 l7 l8⌝ ∗
          rd n de ptr bs (q) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  iintro ⟨#HC, Hc, Hrd, HF⟩
  unfold iterationCode
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hrd HF]
  · iapply SerdeIgnContainer.peek_success cfg lim d inst mi A n g ta hm hd Cg (37 * cfg.regularOpCost + R)
      6 de s ptr 0 l4 l6 l7 l8 l5 bs i Fr hi hlen hptr hde
    iframe HC Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hrd, HF⟩
    rw [← hq, hb] at hfr
    subst hvs; subst hfr
    rw [← hq]
    simp only [Post.mseq_normal]
    unfold blockCode
    rw [List.append_assoc]
    mstep
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc Hrd HF]
    · iapply SerdeIgnContainer.dispatch_first cfg lim d inst mi Cg (cfg.regularOpCost + R)
        de s l4 l6 l7 l8 c h93 h125 h44 (iprop(rd n de ptr bs q ∗ Fr))
      iframe Hrd HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    isplit
    · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, Hrd, HF⟩
      subst hk; subst hvs; subst hfr
      simp only [Post.mseq_br, Post.mblock_br_zero, List.length_nil, List.drop_nil, List.nil_append]
      isplitr
      · ipureintro; omega
      mpay
      iframe Hc Hrd HF
      ipureintro; trivial
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- The entire actual container iteration selects the accepted comma, preserving caller resources. -/
theorem iteration_comma (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l4 l6 l7 l8 : UInt32) (l5 : UInt64) (bs : List UInt8) (i q : Nat)
    (Fr : IProp GF) (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some 0x2C) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ credits Cg ((191 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 1 l4 l5 l6 l7 l8) [] iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 1 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 l4 (optByte (some 0x2C)) 0x2C l7 l8⌝ ∗
          rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  iintro ⟨#HC, Hc, Hrd, HF⟩
  unfold iterationCode
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hrd HF]
  · iapply SerdeIgnContainer.peek_success cfg lim d inst mi A n g ta hm hd Cg (66 * cfg.regularOpCost + R)
      6 de s ptr 1 l4 l6 l7 l8 l5 bs i Fr hi hlen hptr hde
    iframe HC Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hrd, HF⟩
    rw [← hq, hb] at hfr
    subst hvs; subst hfr
    rw [← hq]
    simp only [Post.mseq_normal]
    unfold blockCode
    rw [List.append_assoc]
    mstep
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc Hrd HF]
    · iapply SerdeIgnContainer.dispatch_comma cfg lim d inst mi A n g ta hm (by omega) Cg R
        de s ptr l4 l6 l7 l8 bs q Fr hq_lt hlen hde
      iframe HC Hrd HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    isplit
    · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, Hrd, HF⟩
      subst hk; subst hvs; subst hfr
      simp only [Post.mseq_br, Post.mblock_br_succ, List.nil_append]
      iframe Hc Hrd HF
      ipureintro; trivial
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

end Proof
end WNear.Binary.SerdeIgnClosing
