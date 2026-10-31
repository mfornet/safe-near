import Bridge.Functions.SerdeIgnRoom
import Bridge.Functions.SerdeIgnContainer
import Bridge.Functions.SerdeIgnBudget
import Bridge.Functions.SerdeIgnClosing
import Bridge.Functions.SerdeIgnValueEntry

namespace WNear.Binary.SerdeIgnContainer
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.SerdeRead (rd wsLen optByte)
open WNear.Binary.SerdeIgnValue (fr81)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem dispatch_close_tight (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (Cg R : Nat) (de s l3 l4 l6 l7 : UInt32) (f : UInt8) (hf : Br f) (Fr : IProp GF) :
    credits Cg (30 * cfg.regularOpCost + R) ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 (optByte (some (closing f))) l6 l7 f.toUInt32) [] dispatchCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some (closing f))) (closing f).toUInt32 l7 f.toUInt32⌝ ∗ Fr) } := by
  rcases hf with rfl | rfl <;>
    simp only [show (0x5B : UInt8).toUInt32 = (0x5B : UInt32) from by decide +kernel,
      show (0x7B : UInt8).toUInt32 = (0x7B : UInt32) from by decide +kernel] <;>
    iintro ⟨Hc, HF⟩ <;>
    unfold dispatchCode errorBody eofObjectBody eofArrayBody byteBody commaBody presentBody <;>
    simp only [fr81, closing, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_true, ite_false] <;>
    repeat mstep
  all_goals mcredits R
  all_goals iframe Hc HF
  all_goals ipureintro; trivial

end WNear.Binary.SerdeIgnContainer

namespace WNear.Binary.SerdeIgnClosing

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnContainer (closing)


variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem block_nonempty_tight (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current saved : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8) (i : Nat) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hi : i < bs.length) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (142 * cfg.regularOpCost + R) ∗
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
  · iapply SerdeIgnContainer.dispatch_close_tight cfg lim d inst mi Cg (111 * cfg.regularOpCost + R)
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

theorem block_empty_tight (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i : Nat) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hi : i < bs.length) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (141 * cfg.regularOpCost + R) ∗
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
  · iapply SerdeIgnContainer.dispatch_close_tight cfg lim d inst mi Cg (110 * cfg.regularOpCost + R)
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

theorem iteration_nonempty_tight (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current saved : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8) (i q : Nat) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg ((267 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗
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
      (142 * cfg.regularOpCost + R) 6 de s ptr l3 l4 l6 l7 current.toUInt32 l5 bs i
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
    iapply block_nonempty_tight cfg lim d inst mi A n g ta hm (by omega) Cg R
      s de ptr p cap l3 l4 l6 l7 current saved hcurrent maxP hl F live frames bs q Fr hs hde hlen hq_lt
    iframe HC Hc H32 Hst Hrd HF
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

theorem iteration_empty_tight (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current : UInt8) (hcurrent : Br current)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i q : Nat) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg ((266 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗
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
      (141 * cfg.regularOpCost + R) 6 de s ptr l3 l4 l6 l7 current.toUInt32 l5 bs i
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
    iapply block_empty_tight cfg lim d inst mi A n g ta hm (by omega) Cg R
      s de ptr p cap l3 l4 l6 l7 current hcurrent maxP hl F live bs q Fr hs hde hlen hq_lt
    iframe HC Hc H32 Hst Hrd HF
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

end WNear.Binary.SerdeIgnClosing

namespace WNear.Binary.SerdeIgnWeightedBudget
open Wasm Wasm.Near
/-- Preserve the original scalar-byte rate while reserving a discount for actual future frame pushes. -/
def regular (cfg : WasmConfig) (fixed remaining depth pushes : Nat) : Nat :=
  (fixed + 470 * remaining - 184 * depth - 74 * pushes) * cfg.regularOpCost

theorem reserve_le (remaining depth pushes fixed : Nat) (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    184 * depth + 74 * pushes ≤ fixed + 470 * remaining := by omega

theorem regular_reserve (cfg : WasmConfig) (fixed remaining depth pushes : Nat)
    (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    regular cfg fixed remaining depth pushes + (184 * depth + 74 * pushes) * cfg.regularOpCost =
      (fixed + 470 * remaining) * cfg.regularOpCost := by
  have h := reserve_le remaining depth pushes fixed hd hp
  unfold regular
  rw [Nat.sub_sub, ← Nat.add_mul, Nat.sub_add_cancel h]

theorem opening_cost (cfg : WasmConfig) (f : UInt8) (w remaining depth pushes : Nat)
    (hd : depth + 1 ≤ remaining) (hp : pushes ≤ remaining) :
    (390 + 96 * w) * cfg.regularOpCost +
      regular cfg (SerdeIgnBudget.openedAllowance f) remaining (depth + 1) pushes ≤
      regular cfg (if depth = 0 then 109 else 60) (w + 1 + remaining) depth
        (pushes + if depth = 0 then 0 else 1) := by
  have h : 390 + 96 * w +
      (SerdeIgnBudget.openedAllowance f + 470 * remaining - 184 * (depth + 1) - 74 * pushes) ≤
      (if depth = 0 then 109 else 60) + 470 * (w + 1 + remaining) - 184 * depth -
        74 * (pushes + if depth = 0 then 0 else 1) := by
    unfold SerdeIgnBudget.openedAllowance
    split <;> split <;> omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

theorem pushes_le_remaining (N : Nat) (mode : WNear.IgnoreModel.Mode) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i : Nat)
    (h : SerdeIgnMachineTrace.run WNear.IgnoreModel.vSkip SerdeIgnMachineTrace.keyBody N mode frames (bs.drop i) = some (r, ops)) :
    SerdeIgnTrace.pushCount ops ≤ bs.length - r.length - i := by
  have hg := SerdeIgnMachineTrace.run_good WNear.IgnoreModel.vSkip SerdeIgnMachineTrace.keyBody
    (fun _ _ => WNear.IgnoreModel.vSkip_length) SerdeIgnMachineTrace.keyBody_length N mode frames (bs.drop i)
  have hp := (hg r ops h).2.2
  simp only [List.length_drop] at hp
  omega

/-- Uses the checked 70-operation tightening of the actual close dispatch; full f81 composition is still required. -/
theorem closing_cost (cfg : WasmConfig) (w remaining depth pushes : Nat)
    (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    (285 + 96 * w) * cfg.regularOpCost + regular cfg 0 remaining depth pushes ≤
      regular cfg 0 (w + 1 + remaining) (depth + 1) pushes := by
  have h : 285 + 96 * w + (0 + 470 * remaining - 184 * depth - 74 * pushes) ≤
      0 + 470 * (w + 1 + remaining) - 184 * (depth + 1) - 74 * pushes := by omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

theorem scalar_budget (cfg : WasmConfig) (w consumed remaining depth pushes : Nat)
    (hc : 0 < consumed) (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    (125 + 96 * w) * cfg.regularOpCost + 7 * cfg.regularOpCost +
      (470 * consumed - 73) * cfg.regularOpCost +
      (5 * cfg.regularOpCost + regular cfg 0 remaining depth pushes) ≤
      regular cfg 64 (w + consumed + remaining) depth pushes := by
  have h : 125 + 96 * w + 7 + (470 * consumed - 73) +
      (5 + (0 + 470 * remaining - 184 * depth - 74 * pushes)) ≤
      64 + 470 * (w + consumed + remaining) - 184 * depth - 74 * pushes := by omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

theorem regular_consumed (cfg : WasmConfig) (fixed consumed remaining depth pushes : Nat)
    (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    regular cfg fixed (consumed + remaining) depth pushes =
      470 * consumed * cfg.regularOpCost + regular cfg fixed remaining depth pushes := by
  have h := reserve_le remaining depth pushes fixed hd hp
  have he : fixed + 470 * (consumed + remaining) - 184 * depth - 74 * pushes =
      470 * consumed + (fixed + 470 * remaining - 184 * depth - 74 * pushes) := by omega
  simpa only [regular, Nat.add_mul] using congrArg (fun n => n * cfg.regularOpCost) he

theorem regular_fixed (cfg : WasmConfig) (fixed remaining depth pushes : Nat)
    (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    regular cfg fixed remaining depth pushes = fixed * cfg.regularOpCost + regular cfg 0 remaining depth pushes := by
  have h := reserve_le remaining depth pushes 0 hd hp
  have he : fixed + 470 * remaining - 184 * depth - 74 * pushes =
      fixed + (0 + 470 * remaining - 184 * depth - 74 * pushes) := by omega
  simpa only [regular, Nat.add_mul] using congrArg (fun n => n * cfg.regularOpCost) he

theorem first_cost (cfg : WasmConfig) (f : UInt8) (w remaining depth pushes : Nat)
    (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    (175 + 96 * w + SerdeIgnBudget.memberAllowance f) * cfg.regularOpCost + regular cfg 0 remaining depth pushes ≤
      regular cfg (SerdeIgnBudget.openedAllowance f) (w + remaining) depth pushes := by
  have h : 175 + 96 * w + SerdeIgnBudget.memberAllowance f +
      (0 + 470 * remaining - 184 * depth - 74 * pushes) ≤
      SerdeIgnBudget.openedAllowance f + 470 * (w + remaining) - 184 * depth - 74 * pushes := by
    unfold SerdeIgnBudget.memberAllowance SerdeIgnBudget.openedAllowance
    split <;> omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

theorem comma_cost (cfg : WasmConfig) (f : UInt8) (w remaining depth pushes : Nat)
    (hd : depth ≤ remaining) (hp : pushes ≤ remaining) :
    (200 + 96 * w + SerdeIgnBudget.memberAllowance f) * cfg.regularOpCost + regular cfg 0 remaining depth pushes ≤
      regular cfg 0 (w + 1 + remaining) depth pushes := by
  have h : 200 + 96 * w + SerdeIgnBudget.memberAllowance f +
      (0 + 470 * remaining - 184 * depth - 74 * pushes) ≤
      0 + 470 * (w + 1 + remaining) - 184 * depth - 74 * pushes := by
    unfold SerdeIgnBudget.memberAllowance
    split <;> omega
  simpa only [regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

end WNear.Binary.SerdeIgnWeightedBudget

namespace WNear.Binary.SerdeIgnClosing

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnContainer (closing)

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem funded_nonempty_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current saved : UInt8) (hcurrent : Br current)
    (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8) (i q : Nat) (opened : Bool) (ops : List SerdeIgnTrace.Op) (r : List UInt8) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current))
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) (saved :: frames) (bs.drop i) = some (r, ops)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 2) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap (saved :: frames).length ops + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (saved :: frames) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 current.toUInt32) [] iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ ops',
          ⌜ops = false :: ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.cont saved) frames (bs.drop (q + 1)) = some (r, ops')⌝ ∗
          credits Cg (18 * cfg.regularOpCost +
            SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops') +
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
  have hpush := SerdeIgnWeightedBudget.pushes_le_remaining N (.cont saved) frames bs r ops' (q + 1) hsub
  have hcharge := SerdeIgnWeightedBudget.closing_cost cfg (wsLen (bs.drop i))
    (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops') hdepth hpush
  have hextra : SerdeIgnTrace.extraCost cfg F cap (saved :: frames).length ops =
      SerdeIgnTrace.extraCost cfg F cap frames.length ops' := by
    rw [hops, SerdeIgnMachineStack.pop_extraCost]
  have hcost : (267 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
      (18 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q + 1))
        (frames.length + 1) (SerdeIgnTrace.pushCount ops') + SerdeIgnTrace.extraCost cfg F cap frames.length ops' + R) ≤
      SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 2) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap (saved :: frames).length ops + R := by
    rw [hextra, hsplit, hops]
    simp only [SerdeIgnTrace.pushCount, Bool.false_eq_true, ite_false, Nat.zero_add]
    simp only [Nat.add_mul, Nat.add_assoc, Nat.reduceAdd] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply iteration_nonempty_tight cfg lim d inst mi A n g ta hm hd Cg
      (18 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q + 1))
        (frames.length + 1) (SerdeIgnTrace.pushCount ops') + SerdeIgnTrace.extraCost cfg F cap frames.length ops' + R)
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

theorem funded_empty_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap l3 l4 l6 l7 : UInt32) (current : UInt8) (hcurrent : Br current)
    (maxP hl F N : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i q : Nat) (opened : Bool) (ops : List SerdeIgnTrace.Op) (r : List UInt8) (l5 : UInt64) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some (closing current))
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) [] (bs.drop i) = some (r, ops)) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) 1 (SerdeIgnTrace.pushCount ops) +
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
  have hz : SerdeIgnWeightedBudget.regular cfg 0 0 0 0 = 0 := by simp [SerdeIgnWeightedBudget.regular]
  have hcharge := SerdeIgnWeightedBudget.closing_cost cfg (wsLen (bs.drop i)) 0 0 0 (by omega) (by omega)
  rw [hz] at hcharge
  simp only [Nat.add_zero, Nat.zero_add] at hcharge
  have hcost : (266 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + (19 * cfg.regularOpCost + R) ≤
      SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) 1 (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap 0 ops + R := by
    rw [hextra, hsplit, ← hops]
    simp only [SerdeIgnTrace.pushCount]
    simp only [Nat.add_mul] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, H32, Hst, Hrd, HF⟩
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd HF]
  · iapply iteration_empty_tight cfg lim d inst mi A n g ta hm hd Cg (19 * cfg.regularOpCost + R)
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

end WNear.Binary.SerdeIgnClosing

namespace WNear.Binary.SerdeIgnOpening

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte)
open WNear.Binary.SerdeIgnValue (fr81 ob16 band255)
open WNear.Binary.SerdeIgnMachineStack

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem entry_funded_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
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
      credits Cg (SerdeIgnWeightedBudget.regular cfg (if frames.length = 0 then 109 else 60)
          (bs.length - r.length - i) frames.length (SerdeIgnTrace.pushCount ops) + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d
      (fr81 inst mi de s (flag frames) l4 l5 l6 l7 (current fallback frames)) [] entryCode
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = saveOps frames ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.opened opened) frames (bs.drop (q + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' +
            (6 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
              (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops') + R)) ∗
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
  obtain ⟨ops', hsub, hops⟩ := SerdeIgnSegments.save_some hsave
  have hdepth : frames.length + 1 ≤ bs.length - r.length - (q + 1) := by
    simpa only [SerdeIgnBudget.active] using
      SerdeIgnBudget.active_le_remaining N (.opened opened) frames bs r ops' (q + 1) hsub
  have hsplit : bs.length - r.length - i =
      SerdeRead.wsLen (bs.drop i) + 1 + (bs.length - r.length - (q + 1)) := by omega
  have hpush := SerdeIgnWeightedBudget.pushes_le_remaining N (.opened opened) frames bs r ops' (q + 1) hsub
  have hpushes : SerdeIgnTrace.pushCount ops = SerdeIgnTrace.pushCount ops' + (if frames.length = 0 then 0 else 1) := by
    rw [hops]
    cases frames <;> simp [saveOps, SerdeIgnTrace.pushCount, Nat.add_comm]
  have hcharge := SerdeIgnWeightedBudget.opening_cost cfg opened (SerdeRead.wsLen (bs.drop i))
    (bs.length - r.length - (q + 1)) frames.length (SerdeIgnTrace.pushCount ops') hdepth hpush
  have hcost : (384 + 96 * SerdeRead.wsLen (bs.drop i)) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops +
      (6 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
        (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops') + R) ≤
      SerdeIgnWeightedBudget.regular cfg (if frames.length = 0 then 109 else 60)
        (bs.length - r.length - i) frames.length (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R := by
    rw [hsplit, hpushes]
    simp only [Nat.add_mul] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H80 Hvt Hst Hrd HF]
  ·
    iapply entry cfg lim d inst mi A n g ta hm hd Cg
      (6 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
        (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops') + R)
      gt s de ptr p cap idx fallback l4 l6 l7 l5 opened maxP hl F N live frames bs r ops i q Fr
      hopen hs hde hcap hlen hptr hi hq hb hframes hr hsave
    iframe HC Hg H80 Hvt Hst Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨%os, %htrace, Hc, HR⟩
    have heq : ops' = os := congrArg Prod.snd (Option.some.inj (hsub.symm.trans htrace.2))
    subst os
    iexists ops'
    iframe Hc HR
    ipureintro; exact htrace
  isplit
  · iintro %k %vs %fr H; iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

end WNear.Binary.SerdeIgnOpening

namespace WNear.Binary.SerdeIgnValueEntry
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem pending_entry_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l6 l7 : UInt32) (l5 : UInt64)
    (bs r frames : List UInt8) (ops : List SerdeIgnTrace.Op) (i q maxP F N : Nat) (b f : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some b) (hws : NearInterface.Json.isWhitespace b = false)
    (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val (f :: frames)
      (bs.drop i) = some (r, ops)) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnWeightedBudget.regular cfg 64 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 1 0 l5 l6 l7 f.toUInt32) [] SerdeIgnOpening.entryCode
      { normal := fun vs fr => iprop(∃ e,
          ⌜q < e ∧ e ≤ bs.length - r.length ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.cont f) frames (bs.drop e) = some (r, ops)⌝ ∗
          credits Cg (5 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - e) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some b)) 0 b.toUInt32 f.toUInt32⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  obtain ⟨rest, e, hv, he, hqe, heQ, hsub⟩ := scalar_indices N f frames bs r ops i q b hq hb hb5B hb7B hmodel
  have hdepth : frames.length + 1 ≤ bs.length - r.length - e := by
    simpa only [SerdeIgnBudget.active] using SerdeIgnBudget.active_le_remaining N (.cont f) frames bs r ops e hsub
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + (e - q) + (bs.length - r.length - e) := by omega
  have hpush := SerdeIgnWeightedBudget.pushes_le_remaining N (.cont f) frames bs r ops e hsub
  have hcharge := SerdeIgnWeightedBudget.scalar_budget cfg (wsLen (bs.drop i)) (e - q) (bs.length - r.length - e) (frames.length + 1) (SerdeIgnTrace.pushCount ops) (by omega) hdepth hpush
  rw [← hsplit] at hcharge
  let K := 5 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - e) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
    SerdeIgnTrace.extraCost cfg F cap frames.length ops + R
  iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
  iunfold SerdeIgnMember.code at HC
  icases HC with ⟨#CS, #CE, #F652⟩
  iunfold SerdeIgnSegments.code at CS
  icases CS with ⟨#C81, -⟩
  unfold SerdeIgnOpening.entryCode
  rw [List.append_assoc]
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex Hid HF]
  · iapply SerdeIgnContainer.peek_success cfg lim d inst mi A n g ta hm (by omega) Cg
      (7 * cfg.regularOpCost + (470 * (e - q) - 73) * cfg.regularOpCost + K) 4 de s ptr 1 0 l6 l7 f.toUInt32 l5 bs i
      (iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) hi (by omega) hptr hde
    iframe C81 Hrd Hg H128 He Hhex Hid HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    dsimp only [K]
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hrd, Hg, H128, He, Hhex, Hid, HF⟩
    rw [← hq, hb] at hfr
    subst hvs; subst hfr
    rw [← hq]
    simp only [Post.mseq_normal]
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc Hg H128 Hrd He Hhex Hid HF]
    · iapply SerdeIgnScalar.present cfg lim d inst mi Cg ((470 * (e - q) - 73) * cfg.regularOpCost + K)
        de s 1 0 l6 l7 f.toUInt32 b
        (iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs q ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      iframe Hg H128 Hrd He Hhex Hid HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    isplit
    · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
      subst hvs; subst hfr
      simp only [Post.mseq_normal]
      iapply mwpi_wand
      isplitl [Hc Hg H128 Hrd He Hhex Hid HF]
      · iapply SerdeIgnScalar.pending_block cfg lim d inst mi A n g ta hm hd Cg K
          gt de s ptr 1 l6 l7 f.toUInt32 bs rest q e b Fr hs hde hlen hptr hb he hws hb5B hb7B hv
        iframe C81 CE F652 Hc Hg H128 Hrd He Hhex Hid HF
      iunfold Post.wand
      isplit
      · iintro %vs %fr H
        iexists e
        isplitr
        · ipureintro; exact ⟨hqe, heQ, hsub⟩
        iexact H
      isplit
      · iintro %k %vs %fr H; iexfalso; iexact H
      isplit
      · iintro %vs %fr H; iexfalso; iexact H
      · iintro H; iexfalso; iexact H
    isplit
    · iintro %k %vs %fr H; iexfalso; iexact H
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

end WNear.Binary.SerdeIgnValueEntry

namespace WNear.Binary.SerdeIgnMember

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen optByte)
open WNear.Binary.SerdeIgnValue (fr81)

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem object_traced_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (maxP F N i : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.key SerdeIgnMachineTrace.keyBody (bs.drop i)
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (0x7B :: frames)) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 0x7B) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ j,
          ⌜i ≤ j + 1 ∧ j + 1 ≤ bs.length - r.length ∧
            SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (0x7B :: frames)
              (bs.drop (j + 1)) = some (r, ops)⌝ ∗
          credits Cg (SerdeIgnWeightedBudget.regular cfg 65 (bs.length - r.length - (j + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some 0x3A)) 0 l7 0x7B⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs (j + 1) ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr) } := by
  obtain ⟨q, e, j, key, rest, hq, he, hj, hquote, hcolon, hkey, hqe, hnext⟩ :=
    key_indices bs i _ _ hi hmodel
  have hgood := SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
    (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N .val (0x7B :: frames) (bs.drop (j + 1))
  have hrest := (hgood r ops hnext).2.1
  have hj_lt := SerdeNextKey.getElem_lt hcolon
  simp only [List.length_drop] at hrest
  have hjQ : j + 1 ≤ bs.length - r.length := by omega
  have hQi : i ≤ j + 1 := by omega
  have hsplit : bs.length - r.length - i = (j + 1 - i) + (bs.length - r.length - (j + 1)) := by omega
  have hdepth : frames.length + 1 ≤ bs.length - r.length - (j + 1) := by
    simpa only [SerdeIgnBudget.active, List.length_cons] using
      SerdeIgnBudget.active_le_remaining N .val (0x7B :: frames) bs r ops (j + 1) hnext
  have hpush := SerdeIgnWeightedBudget.pushes_le_remaining N .val (0x7B :: frames) bs r ops (j + 1) hnext
  have hkcost := SerdeIgnMemberBudget.cost_le_entry cfg i q e j (by omega) hqe (by omega)
  have hcost : cost cfg i q e j +
      (SerdeIgnWeightedBudget.regular cfg 65 (bs.length - r.length - (j + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ≤
      SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R := by
    rw [hsplit, SerdeIgnWeightedBudget.regular_consumed cfg 0 _ _ _ _ hdepth hpush,
      SerdeIgnWeightedBudget.regular_fixed cfg 65 _ _ _ hdepth hpush]
    omega
  iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex HF]
  · iapply object_next cfg lim d inst mi A n g ta hm hd Cg
      (SerdeIgnWeightedBudget.regular cfg 65 (bs.length - r.length - (j + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
      gt de s ptr l3 l4 l6 l7 l5 maxP i q e j bs rest key Fr hs hde hlen hptr hi hq he hj hquote hcolon hkey
    iframe HC Hg H128 Hrd He Hhex HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexact H
  isplit
  · iintro %k %vs %fr H
    iexists j
    isplitr
    · ipureintro; exact ⟨hQi, hjQ, hnext⟩
    iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H


theorem next_traced_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (f : UInt8) (maxP F N i : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hf : Br f) (hmodel : nextModel N f frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnWeightedBudget.regular cfg (if f = 0x5B then 75 else 0) (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 f.toUInt32) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ (j : Nat) (l5' : UInt64) (l6' : UInt32),
          ⌜i ≤ j ∧ j ≤ bs.length - r.length ∧
            SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (f :: frames)
              (bs.drop j) = some (r, ops) ∧
            k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 l5' l6' l7 f.toUInt32⌝ ∗
          credits Cg (SerdeIgnWeightedBudget.regular cfg 65 (bs.length - r.length - j) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs j ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr) } := by
  rcases hf with rfl | rfl
  · rw [show (0x5B : UInt8).toUInt32 = (0x5B : UInt32) from by decide +kernel]
    simp only [nextModel, ite_true] at hmodel
    have hgood := SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
      (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N .val (0x5B :: frames) (bs.drop i)
    have hrest := (hgood r ops hmodel).2.1
    simp only [List.length_drop] at hrest
    have hdepth : frames.length + 1 ≤ bs.length - r.length - i := by
      simpa only [SerdeIgnBudget.active, List.length_cons] using
        SerdeIgnBudget.active_le_remaining N .val (0x5B :: frames) bs r ops i hmodel
    have hpush := SerdeIgnWeightedBudget.pushes_le_remaining N .val (0x5B :: frames) bs r ops i hmodel
    have hiQ : i ≤ bs.length - r.length := by omega
    iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
    iapply mwpi_wand
    isplitl [Hc Hg H128 Hrd He Hhex HF]
    · iapply array_next cfg lim d inst mi Cg
        (SerdeIgnWeightedBudget.regular cfg 65 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
        de s l3 l4 l6 l7 l5 iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr)
      iframe Hg H128 Hrd He Hhex HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      simp only [ite_true, SerdeIgnWeightedBudget.regular_fixed cfg 75 _ _ _ hdepth hpush,
        SerdeIgnWeightedBudget.regular_fixed cfg 65 _ _ _ hdepth hpush]
      omega
    iunfold Post.wand
    isplit
    · iintro %vs %fr H; iexact H
    isplit
    · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, HF⟩
      iexists i, l5, l6
      iframe Hc Hg H128 Hrd He Hhex HF
      ipureintro; exact ⟨by omega, hiQ, hmodel, hk, hvs, hfr⟩
    isplit
    · iintro %vs %fr H; iexact H
    · iintro H; iexact H
  · rw [show (0x7B : UInt8).toUInt32 = (0x7B : UInt32) from by decide +kernel]
    simp only [nextModel, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at hmodel
    iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
    iapply mwpi_wand
    isplitl [Hc Hg H128 Hrd He Hhex HF]
    · iapply object_traced_weighted cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr cap l3 l4 l6 l7 l5
        maxP F N i frames bs r ops Fr hs hde hlen hptr hi hmodel
      iframe HC Hg H128 Hrd He Hhex HF
      simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false, Nat.zero_add]
      iexact Hc
    iunfold Post.wand
    isplit
    · iintro %vs %fr H; iexact H
    isplit
    · iintro %k %vs %fr ⟨%j, %⟨hij, hjQ, hn⟩, Hc, %⟨hk, hvs, hfr⟩, Hg, H128, Hrd, He, Hhex, HF⟩
      iexists j + 1, optByte (some 0x3A), 0
      iframe Hc Hg H128 Hrd He Hhex HF
      ipureintro; exact ⟨hij, hjQ, hn, hk, hvs, hfr⟩
    isplit
    · iintro %vs %fr H; iexact H
    · iintro H; iexact H

end WNear.Binary.SerdeIgnMember

namespace WNear.Binary.SerdeIgnMemberBudget

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnMember

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem next_pushes (N : Nat) (f : UInt8) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (i : Nat) (hf : Br f) (hi : i ≤ bs.length)
    (h : nextModel N f frames (bs.drop i) = some (r, ops)) :
    SerdeIgnTrace.pushCount ops ≤ bs.length - r.length - i := by
  rcases hf with rfl | rfl
  · simp only [nextModel, ite_true] at h
    exact SerdeIgnWeightedBudget.pushes_le_remaining N .val (0x5B :: frames) bs r ops i h
  · simp only [nextModel, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at h
    obtain ⟨q, e, j, key, rest, hq, he, hj, hquote, hcolon, hkey, hqe, hnext⟩ := key_indices bs i _ _ hi h
    have hp := SerdeIgnWeightedBudget.pushes_le_remaining N .val (0x7B :: frames) bs r ops (j + 1) hnext
    omega

theorem next_funded_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (f : UInt8) (maxP F N i : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hf : Br f) (hmodel : nextModel N f frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 f.toUInt32) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ (j : Nat) (l5' : UInt64) (l6' : UInt32),
          ⌜i ≤ j ∧ j ≤ bs.length - r.length ∧
            SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (f :: frames)
              (bs.drop j) = some (r, ops) ∧
            k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 l5' l6' l7 f.toUInt32⌝ ∗
          credits Cg (cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg 64 (bs.length - r.length - j) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs j ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr) } := by
  have hdepth := next_depth N f frames bs r ops i hf hi hmodel
  have hpush := next_pushes N f frames bs r ops i hf hi hmodel
  have hreg := SerdeIgnWeightedBudget.regular_fixed cfg (SerdeIgnBudget.memberAllowance f)
    (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) hdepth hpush
  iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex HF]
  · iapply next_traced_weighted cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr cap l3 l4 l6 l7 l5
      f maxP F N i frames bs r ops Fr hs hde hlen hptr hi hf hmodel
    iframe HC Hg H128 Hrd He Hhex HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    change SerdeIgnWeightedBudget.regular cfg (SerdeIgnBudget.memberAllowance f) _ _ _ + _ + _ ≤ _
    rw [hreg]
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexact H
  isplit
  · iintro %k %vs %fr ⟨%j, %l5', %l6', %hj, Hc, HR⟩
    have hd' : frames.length + 1 ≤ bs.length - r.length - j := by
      simpa only [SerdeIgnBudget.active, List.length_cons] using
        SerdeIgnBudget.active_le_remaining N .val (f :: frames) bs r ops j hj.2.2.1
    have hp' := SerdeIgnWeightedBudget.pushes_le_remaining N .val (f :: frames) bs r ops j hj.2.2.1
    have h65 := SerdeIgnWeightedBudget.regular_fixed cfg 65 _ _ _ hd' hp'
    have h64 := SerdeIgnWeightedBudget.regular_fixed cfg 64 _ _ _ hd' hp'
    have heq : SerdeIgnWeightedBudget.regular cfg 65 (bs.length - r.length - j) (frames.length + 1) (SerdeIgnTrace.pushCount ops) =
        cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg 64 (bs.length - r.length - j) (frames.length + 1) (SerdeIgnTrace.pushCount ops) := by omega
    iexists j, l5', l6'
    isplitr
    · ipureintro; exact hj
    rw [← heq]
    iframe Hc HR
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

theorem first_funded_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l4 l6 l7 : UInt32) (l5 : UInt64) (f : UInt8) (c : UInt8) (cap : UInt32)
    (maxP F N i q : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hf : Br f) (h93 : c ≠ 0x5D) (h125 : c ≠ 0x7D) (h44 : c ≠ 0x2C) (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some c)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) (.opened f) frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnWeightedBudget.regular cfg (SerdeIgnBudget.openedAllowance f) (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 0 l4 l5 l6 l7 f.toUInt32) [] SerdeIgnClosing.iterationCode
      { normal := fun vs fr => iprop(⌜nextModel N f frames (bs.drop (q)) = some (r, ops)⌝ ∗
          credits Cg (13 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
            SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some c)) c.toUInt32 l7 f.toUInt32⌝ ∗
          rd n de ptr bs (q) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hq_lt hb
  have hs : NearInterface.Json.skipWhitespace (bs.drop i) = c :: bs.drop (q + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop, ← hq, hdr]
  have hnext := first_next N f c frames (bs.drop i) _ r ops hf hs h93 h125 hmodel
  rw [← hdr] at hnext
  have hdepth := next_depth N f frames bs r ops (q) hf (by omega) hnext
  have hpush := next_pushes N f frames bs r ops (q) hf (by omega) hnext
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + (bs.length - r.length - (q)) := by omega
  have hcharge := SerdeIgnWeightedBudget.first_cost cfg f (wsLen (bs.drop i))
    (bs.length - r.length - (q)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) hdepth hpush
  have hcost : (162 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
      (13 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ≤
      SerdeIgnWeightedBudget.regular cfg (SerdeIgnBudget.openedAllowance f) (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R := by
    rw [hsplit]
    simp only [Nat.add_mul] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, Hrd, HF⟩
  ihave #HC' := HC
  iunfold code at HC'
  icases HC' with ⟨#CS, -⟩
  iunfold SerdeIgnSegments.code at CS
  icases CS with ⟨#C81, -⟩
  iapply mwpi_wand
  isplitl [Hc Hrd HF]
  · iapply SerdeIgnClosing.iteration_first cfg lim d inst mi A n g ta hm hd Cg
      (13 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
      de s ptr l4 l6 l7 f.toUInt32 l5 c bs i q Fr h93 h125 h44 hi hlen hptr hde hq hb
    iframe C81 Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H
    isplitr
    · ipureintro; exact hnext
    iexact H
  isplit
  · iintro %k %vs %fr H; iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

theorem comma_funded_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l4 l6 l7 : UInt32) (l5 : UInt64) (f : UInt8) (cap : UInt32)
    (maxP F N i q : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hf : Br f) (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some 0x2C)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) (.cont f) frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 1 l4 l5 l6 l7 f.toUInt32) [] SerdeIgnClosing.iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(⌜nextModel N f frames (bs.drop (q + 1)) = some (r, ops)⌝ ∗
          credits Cg (9 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
            SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜k = 1 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 l4 (optByte (some 0x2C)) 0x2C l7 f.toUInt32⌝ ∗
          rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hq_lt hb
  have hs : NearInterface.Json.skipWhitespace (bs.drop i) = 0x2C :: bs.drop (q + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop, ← hq, hdr]
  have hnext := comma_next N f frames (bs.drop i) _ r ops hf hs hmodel
  have hdepth := next_depth N f frames bs r ops (q + 1) hf (by omega) hnext
  have hpush := next_pushes N f frames bs r ops (q + 1) hf (by omega) hnext
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + 1 + (bs.length - r.length - (q + 1)) := by omega
  have hcharge := SerdeIgnWeightedBudget.comma_cost cfg f (wsLen (bs.drop i))
    (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) hdepth hpush
  have hcost : (191 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
      (9 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ≤
      SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R := by
    rw [hsplit]
    simp only [Nat.add_mul] at hcharge ⊢
    omega
  iintro ⟨#HC, Hc, Hrd, HF⟩
  ihave #HC' := HC
  iunfold code at HC'
  icases HC' with ⟨#CS, -⟩
  iunfold SerdeIgnSegments.code at CS
  icases CS with ⟨#C81, -⟩
  iapply mwpi_wand
  isplitl [Hc Hrd HF]
  · iapply SerdeIgnClosing.iteration_comma cfg lim d inst mi A n g ta hm hd Cg
      (9 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
      de s ptr l4 l6 l7 f.toUInt32 l5 bs i q Fr hi hlen hptr hde hq hb
    iframe C81 Hrd HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H; iexact H
  isplit
  · iintro %k %vs %fr H
    isplitr
    · ipureintro; exact hnext
    iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H
end WNear.Binary.SerdeIgnMemberBudget

namespace WNear.Binary.SerdeIgnWeightedLoop
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnContainer (closing)

/-- Exact original frame/operation prefixes removed by successive real pops. -/
def Pops (initial frames : List UInt8) (original ops : List SerdeIgnTrace.Op) : Prop :=
  ∃ popped, initial = popped ++ frames ∧ original = List.replicate popped.length false ++ ops

theorem Pops.refl (frames : List UInt8) (ops : List SerdeIgnTrace.Op) : Pops frames frames ops ops :=
  ⟨[], rfl, rfl⟩

theorem Pops.step {initial frames : List UInt8} {saved : UInt8} {original ops : List SerdeIgnTrace.Op}
    (h : Pops initial (saved :: frames) original (false :: ops)) : Pops initial frames original ops := by
  obtain ⟨popped, hi, ho⟩ := h
  refine ⟨popped ++ [saved], ?_, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using hi
  · rw [List.length_append, List.length_singleton, List.replicate_add]
    simpa only [List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append, List.append_assoc] using ho

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def resources (n : Nat) (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (bs : List UInt8) (i : Nat) (frames : List UInt8) (Fr : IProp GF) : IProp GF :=
  iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗
    rd n de ptr bs i ∗ Fr)

def memberExit (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n Cg R : Nat)
    (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (allowance : Nat) (comma : Bool) (Fr : IProp GF)
    (vs : List Value) (fr : Frame) : IProp GF :=
  iprop(∃ (i N : Nat) (current : UInt8) (frames : List UInt8) (ops : List SerdeIgnTrace.Op)
      (l3 l4 l6 l7 : UInt32) (l5 : UInt64),
    ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 l5 l6 l7 current.toUInt32 ∧ Br current ∧
      (∀ f ∈ frames, Br f) ∧ i ≤ bs.length ∧ Pops initial frames original ops ∧
      SerdeIgnMember.nextModel N current frames (bs.drop i) = some (r, ops) ∧ l3 = (if comma then 1 else 0)⌝ ∗
    credits Cg (allowance * cfg.regularOpCost + SerdeIgnBudget.memberAllowance current * cfg.regularOpCost +
      SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
      SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
    resources n s de ptr p cap maxP hl F live bs i frames Fr)

def successExit (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n Cg R : Nat)
    (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (vs : List Value) (fr : Frame) : IProp GF :=
  iprop(∃ (i : Nat) (l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64),
    ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 l5 l6 l7 l8 ∧
      i = bs.length - r.length ∧ i ≤ bs.length ∧ Pops initial [] original []⌝ ∗
    credits Cg (19 * cfg.regularOpCost + R) ∗
    resources n s de ptr p cap maxP hl F live bs i [] Fr)

def invariant (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n Cg R : Nat)
    (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (vs : List Value) (fr : Frame) : IProp GF :=
  iprop(∃ (i N : Nat) (opened : Bool) (current : UInt8) (frames : List UInt8)
      (ops : List SerdeIgnTrace.Op) (l4 l6 l7 : UInt32) (l5 : UInt64),
    ⌜vs = [] ∧ fr = fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 current.toUInt32 ∧
      Br current ∧ (∀ f ∈ frames, Br f) ∧ i ≤ bs.length ∧ Pops initial frames original ops ∧
      SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
        (if opened then .opened current else .cont current) frames (bs.drop i) = some (r, ops)⌝ ∗
    credits Cg (SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
        (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
      SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
    resources n s de ptr p cap maxP hl F live bs i frames Fr)

def post (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n Cg R : Nat)
    (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (Fr : IProp GF) : Post NearState GF :=
  { normal := memberExit cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original 9 false Fr
    br := fun k vs fr => iprop((⌜k = 0⌝ ∗ memberExit cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original 9 true Fr vs fr) ∨
            (⌜k = 3⌝ ∗ successExit cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original Fr vs fr)) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem iteration (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (vs : List Value) (fr : Frame) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      invariant cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original Fr vs fr ⊢
    mwpi cfg lim d fr vs SerdeIgnClosing.iterationCode
      (Post.mloop cfg Cg 0 []
        (invariant cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original Fr)
        (post cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original Fr)) := by
  iintro ⟨#HC, HI⟩
  iunfold invariant at HI
  icases HI with ⟨%i, %N, %opened, %current, %frames, %ops, %l4, %l6, %l7, %l5,
    %⟨hvs, hfr, hcurrent, hframes, hi, hpops, hmodel⟩, Hc, HR⟩
  subst hvs; subst hfr
  obtain ⟨c, t, hskip⟩ := SerdeIgnContainer.phase_nonempty N opened current frames (bs.drop i) r ops hmodel
  let q := i + wsLen (bs.drop i)
  have hdr : NearInterface.Json.skipWhitespace (bs.drop i) = bs.drop q := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
  have hb : bs[q]? = some c := (SerdeStructLoop.drop_cons (hdr.symm.trans hskip)).1
  have hq := SerdeNextKey.getElem_lt hb
  ihave #HS := HC
  iunfold SerdeIgnMember.code at HS
  icases HS with ⟨#HS, -⟩
  rcases SerdeIgnContainer.phase_cases N opened current c frames (bs.drop i) t r ops hcurrent hskip hmodel with hclose | hfirst | hcomma
  · obtain ⟨hc, hpop⟩ := hclose
    subst c
    have hreg : SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) ≤
        SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) := by
      unfold SerdeIgnWeightedBudget.regular
      apply Nat.mul_le_mul_right
      omega
    cases frames with
    | nil =>
      iapply mwpi_wand
      isplitl [Hc HR]
      · iapply SerdeIgnClosing.funded_empty_weighted cfg lim d inst mi A n g ta hm hd Cg R
          s de ptr p cap (if opened then 0 else 1) l4 l6 l7 current hcurrent maxP hl F N live bs i q opened ops r l5 Fr
          hs hde hlen hptr hi rfl hb hmodel
        iunfold resources at HR
        icases HR with ⟨H32, Hst, Hrd, HF⟩
        iframe HS H32 Hst Hrd HF
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; exact Nat.add_le_add_right (Nat.add_le_add_right hreg _) _
      iunfold Post.wand
      isplit
      · iintro %vs' %fr' H; iexfalso; iexact H
      isplit
      · iintro %k %vs' %fr' ⟨%⟨hops, hr, hend⟩, Hc, %⟨hk, hvs', hfr'⟩, H32, Hst, Hrd, HF⟩
        subst hk; subst hvs'; subst hfr'
        simp only [post, Post.mloop, List.nil_append]
        iright
        isplitr
        · ipureintro; trivial
        iunfold successExit
        iexists q + 1, (if opened then 0 else 1), l4, (closing current).toUInt32, l7, current.toUInt32,
          optByte (some (closing current))
        iframe Hc
        isplitr
        · ipureintro
          exact ⟨rfl, rfl, hend.symm, by omega, hops ▸ hpops⟩
        iunfold resources
        iframe H32 Hst Hrd HF
      isplit
      · iintro %vs' %fr' H; iexfalso; iexact H
      · iintro H; iexfalso; iexact H
    | cons saved frames =>
      have hsaved := hframes saved (by simp)
      have htail : ∀ f ∈ frames, Br f := fun f hf => hframes f (by simp [hf])
      iapply mwpi_wand
      isplitl [Hc HR]
      · iapply SerdeIgnClosing.funded_nonempty_weighted cfg lim d inst mi A n g ta hm hd Cg R
          s de ptr p cap (if opened then 0 else 1) l4 l6 l7 current saved hcurrent maxP hl F N live frames bs i q opened ops r l5 Fr
          hs hde hlen hptr hi rfl hb hmodel
        iunfold resources at HR
        icases HR with ⟨H32, Hst, Hrd, HF⟩
        iframe HS H32 Hst Hrd HF
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro
        simpa only [List.length_cons, Nat.add_assoc, Nat.reduceAdd] using
          Nat.add_le_add_right (Nat.add_le_add_right hreg (SerdeIgnTrace.extraCost cfg F cap (saved :: frames).length ops)) R
      iunfold Post.wand
      isplit
      · iintro %vs' %fr' H; iexfalso; iexact H
      isplit
      · iintro %k %vs' %fr' ⟨%ops', %⟨hops, hsub⟩, Hc, %⟨hk, hvs', hfr'⟩, H32, Hst, Hrd, HF⟩
        subst hk; subst hvs'; subst hfr'
        cases N with
        | zero => simp [SerdeIgnMachineTrace.run] at hsub
        | succ N =>
          have hnewpops := Pops.step (hops ▸ hpops)
          simp only [post, Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
          isplitr
          · ipureintro; omega
          mpay with skip
          iunfold invariant
          iexists q + 1, N, false, saved, frames, ops', l4, (closing current).toUInt32, l7, optByte (some (closing current))
          isplitr
          · ipureintro; exact ⟨rfl, rfl, hsaved, htail, by omega, hnewpops, hsub⟩
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro
            simp only [Bool.false_eq_true, ite_false, Nat.add_mul, Nat.sub_sub]
            omega
          iunfold resources
          iframe H32 Hst Hrd HF
      isplit
      · iintro %vs' %fr' H; iexfalso; iexact H
      · iintro H; iexfalso; iexact H
  · obtain ⟨ho, h93, h125, h44, hnext⟩ := hfirst
    subst opened
    simp only [ite_true] at hmodel ⊢
    iapply mwpi_wand
    isplitl [Hc HR]
    · iapply SerdeIgnMemberBudget.first_funded_weighted cfg lim d inst mi A n g ta hm hd Cg R
        de s ptr l4 l6 l7 l5 current c cap maxP F N i q frames bs r ops
        (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗ Fr))
        hcurrent h93 h125 h44 hi hlen hptr (by omega) rfl hb hmodel
      iunfold resources at HR
      icases HR with ⟨H32, Hst, Hrd, HF⟩
      iframe HC Hc Hrd H32 Hst HF
    iunfold Post.wand
    isplit
    · iintro %vs' %fr' ⟨%hnext', Hc, %⟨hvs', hfr'⟩, Hrd, H32, Hst, HF⟩
      subst hvs'; subst hfr'
      simp only [post, Post.mloop, List.nil_append]
      mpay with skip
      iunfold memberExit
      iexists q, N, current, frames, ops, 0, l4, c.toUInt32, l7, optByte (some c)
      isplitr
      · ipureintro; exact ⟨rfl, rfl, hcurrent, hframes, by omega, hpops, hnext', rfl⟩
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro
        simp only [Nat.add_mul, Nat.sub_sub]
        omega
      iunfold resources
      iframe H32 Hst Hrd HF
    isplit
    · iintro %k %vs' %fr' H; iexfalso; iexact H
    isplit
    · iintro %vs' %fr' H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  · obtain ⟨ho, hc, hnext⟩ := hcomma
    subst opened; subst c
    simp only [Bool.false_eq_true, ite_false] at hmodel ⊢
    iapply mwpi_wand
    isplitl [Hc HR]
    · iapply SerdeIgnMemberBudget.comma_funded_weighted cfg lim d inst mi A n g ta hm hd Cg R
        de s ptr l4 l6 l7 l5 current cap maxP F N i q frames bs r ops
        (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗ Fr))
        hcurrent hi hlen hptr (by omega) rfl hb hmodel
      iunfold resources at HR
      icases HR with ⟨H32, Hst, Hrd, HF⟩
      iframe HC Hc Hrd H32 Hst HF
    iunfold Post.wand
    isplit
    · iintro %vs' %fr' H; iexfalso; iexact H
    isplit
    · iintro %k %vs' %fr' ⟨%hnext', Hc, %⟨hk, hvs', hfr'⟩, Hrd, H32, Hst, HF⟩
      subst hk; subst hvs'; subst hfr'
      simp only [post, Post.mloop, List.nil_append]
      ileft
      isplitr
      · ipureintro; trivial
      iunfold memberExit
      iexists q + 1, N, current, frames, ops, 1, l4, 0x2C, l7, optByte (some 0x2C)
      iframe Hc
      isplitr
      · ipureintro; exact ⟨rfl, rfl, hcurrent, hframes, by omega, hpops, hnext', rfl⟩
      iunfold resources
      iframe H32 Hst Hrd HF
    isplit
    · iintro %vs' %fr' H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H

def loopCode : List Instr := [.loop .empty SerdeIgnClosing.iterationCode]

theorem loopCode_at : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 3]).take 1 = loopCode := by rfl

set_option maxRecDepth 100000 in
/-- The real loop consumes its entry charge once and establishes the single-credit invariant. -/
theorem loop (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (i N : Nat) (opened : Bool) (current : UInt8) (l4 l6 l7 : UInt32) (l5 : UInt64)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hcurrent : Br current) (hframes : ∀ f ∈ frames, Br f) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) frames (bs.drop i) = some (r, ops)) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg (cfg.regularOpCost +
        (SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      resources n s de ptr p cap maxP hl F live bs i frames Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 current.toUInt32) [] loopCode
      (post cfg inst mi n Cg R s de ptr p cap maxP hl F live frames bs r ops Fr) := by
  iintro ⟨#HC, Hc, HR⟩
  unfold loopCode
  iapply MemCpy.mwpi_loop0 (Cg := Cg)
    (R := SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
      (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) + SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
    .empty SerdeIgnClosing.iterationCode
    (invariant cfg inst mi n Cg R s de ptr p cap maxP hl F live frames bs r ops Fr) rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iapply iteration cfg lim d inst mi A n g ta hm hd Cg R s de ptr p cap maxP hl F live frames bs r ops Fr
      hs hde hlen hptr X _
    iframe HC HI
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  iunfold invariant
  iexists i, N, opened, current, frames, ops, l4, l6, l7, l5
  iframe Hc HR
  ipureintro
  exact ⟨rfl, rfl, hcurrent, hframes, hi, Pops.refl frames ops, hmodel⟩

/-- The rejecting tail is retained verbatim, and is bypassed by every successful loop exit. -/
noncomputable def errorTail : List Instr := (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 3]).drop 6

noncomputable def phaseCode : List Instr := [.block .empty (loopCode ++ SerdeIgnContainer.exitCode ++ errorTail)]

theorem phaseCode_at : ((SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).drop 3).take 1 = phaseCode := by rfl

def phasePost (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n Cg R : Nat)
    (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (Fr : IProp GF) : Post NearState GF :=
  { normal := fun vs fr => iprop(∃ comma : Bool,
      memberExit cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original 3 comma Fr vs fr)
    br := fun k vs fr => iprop(⌜k = 2⌝ ∗ successExit cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original Fr vs fr) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem phase (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (i N : Nat) (opened : Bool) (current : UInt8) (l4 l6 l7 : UInt32) (l5 : UInt64)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hcurrent : Br current) (hframes : ∀ f ∈ frames, Br f) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) frames (bs.drop i) = some (r, ops)) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg (2 * cfg.regularOpCost +
        (SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      resources n s de ptr p cap maxP hl F live bs i frames Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 current.toUInt32) [] phaseCode
      (phasePost cfg inst mi n Cg R s de ptr p cap maxP hl F live frames bs r ops Fr) := by
  iintro ⟨#HC, Hc, HR⟩
  unfold phaseCode
  rw [List.append_assoc]
  mstep
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc HR]
  · iapply loop cfg lim d inst mi A n g ta hm hd Cg R s de ptr p cap maxP hl F live frames bs r ops Fr
      i N opened current l4 l6 l7 l5 hs hde hlen hptr hcurrent hframes hi hmodel
    iframe HC HR
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul, Nat.sub_sub]
    omega
  iunfold Post.wand
  simp only [post]
  isplit
  · iintro %vs' %fr' H
    iunfold memberExit at H
    icases H with ⟨%j, %M, %f, %fs, %os, %l3', %l4', %l6', %l7', %l5',
      %⟨hvs, hfr, hf, hfs, hj, hpops, hnext, hl3⟩, Hc, HR⟩
    simp only [Bool.false_eq_true, ite_false] at hl3
    subst l3'; subst hvs; subst hfr
    simp only [Post.mseq_normal]
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc HR]
    · iapply SerdeIgnContainer.first_exit cfg lim d inst mi Cg
        (4 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
          SerdeIgnWeightedBudget.regular cfg 0 (bs.length - r.length - j) (fs.length + 1) (SerdeIgnTrace.pushCount os) +
          SerdeIgnTrace.extraCost cfg F cap fs.length os + R)
        de s l4' l6' l7' f.toUInt32 l5' (resources n s de ptr p cap maxP hl F live bs j fs Fr)
      iframe HR
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    isplit
    · iintro %vs'' %fr'' H; iexfalso; iexact H
    isplit
    · iintro %k %vs'' %fr'' ⟨Hc, %⟨hk, hvs, hfr⟩, HR⟩
      subst hk; subst hvs; subst hfr
      simp only [Post.mseq_br, Post.mblock_br_zero, List.length_nil, List.drop_nil, List.nil_append]
      isplitr
      · ipureintro; omega
      mpay with skip
      simp only [phasePost]
      iexists false
      iunfold memberExit
      iexists j, M, f, fs, os, 0, l4', l6', l7', l5'
      iframe HR
      isplitr
      · ipureintro; exact ⟨rfl, rfl, hf, hfs, hj, hpops, hnext, rfl⟩
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      simp only [Nat.add_mul, Nat.sub_sub]
      omega
    isplit
    · iintro %vs'' %fr'' H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  isplit
  · iintro %k %vs' %fr' H
    icases H with (H | H)
    · icases H with ⟨%hk, H⟩
      subst hk
      iunfold memberExit at H
      icases H with ⟨%j, %M, %f, %fs, %os, %l3', %l4', %l6', %l7', %l5',
        %⟨hvs, hfr, hf, hfs, hj, hpops, hnext, hl3⟩, Hc, HR⟩
      subst hvs; subst hfr
      simp only [Post.mseq_br, Post.mblock_br_zero, List.length_nil, List.drop_nil, List.nil_append]
      isplitr
      · ipureintro; omega
      mpay with skip
      simp only [phasePost]
      iexists true
      iunfold memberExit
      iexists j, M, f, fs, os, l3', l4', l6', l7', l5'
      iframe HR
      isplitr
      · ipureintro; exact ⟨rfl, rfl, hf, hfs, hj, hpops, hnext, hl3⟩
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      simp only [Nat.add_mul, Nat.sub_sub]
      omega
    · icases H with ⟨%hk, H⟩
      subst hk
      simp only [Post.mseq_br, Post.mblock_br_succ, List.nil_append, phasePost]
      isplitr
      · ipureintro; trivial
      iexact H
  isplit
  · iintro %vs' %fr' H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

/-- All of the actual value-loop body after successful value dispatch. -/
noncomputable def suffixCode : List Instr := phaseCode ++ SerdeIgnMember.memberCode

theorem suffixCode_at : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).drop 3 = suffixCode := by rfl

def caller (n g : Nat) (gt : GlobalType) (s : UInt32) (Fr : IProp GF) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗
    n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr)

def valueExit (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n g Cg R : Nat) (gt : GlobalType)
    (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (vs : List Value) (fr : Frame) : IProp GF :=
  iprop(∃ (i N : Nat) (current : UInt8) (frames : List UInt8) (ops : List SerdeIgnTrace.Op)
      (l6 l7 : UInt32) (l5 : UInt64),
    ⌜vs = [] ∧ fr = fr81 inst mi de s 1 0 l5 l6 l7 current.toUInt32 ∧ Br current ∧
      (∀ f ∈ frames, Br f) ∧ i ≤ bs.length ∧ Pops initial frames original ops ∧
      SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (current :: frames) (bs.drop i) = some (r, ops)⌝ ∗
    credits Cg (4 * cfg.regularOpCost +
      SerdeIgnWeightedBudget.regular cfg 64 (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
      SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
    resources n s de ptr p cap maxP hl F live bs i frames (caller n g gt s Fr))

def suffixPost (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n g Cg R : Nat) (gt : GlobalType)
    (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (initial bs r : List UInt8) (original : List SerdeIgnTrace.Op) (Fr : IProp GF) : Post NearState GF :=
  { normal := fun _ _ => iprop(False)
    br := fun k vs fr => iprop((⌜k = 0⌝ ∗
        valueExit cfg inst mi n g Cg R gt s de ptr p cap maxP hl F live initial bs r original Fr vs fr) ∨
      (⌜k = 2⌝ ∗ successExit cfg inst mi n Cg R s de ptr p cap maxP hl F live initial bs r original (caller n g gt s Fr) vs fr)) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The complete actual container/member suffix enters the next value or takes success, with its exact trace suffix. -/
theorem suffix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (i N : Nat) (opened : Bool) (current : UInt8) (l4 l6 l7 : UInt32) (l5 : UInt64)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hstack : 128 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hcurrent : Br current) (hframes : ∀ f ∈ frames, Br f) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) frames (bs.drop i) = some (r, ops)) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg (2 * cfg.regularOpCost +
        (SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      resources n s de ptr p cap maxP hl F live bs i frames (caller n g gt s Fr) ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 current.toUInt32) [] suffixCode
      (suffixPost cfg inst mi n g Cg R gt s de ptr p cap maxP hl F live frames bs r ops Fr) := by
  iintro ⟨#HC, Hc, HR⟩
  unfold suffixCode
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc HR]
  · iapply phase cfg lim d inst mi A n g ta hm (by omega) Cg R s de ptr p cap maxP hl F live frames bs r ops
      (caller n g gt s Fr) i N opened current l4 l6 l7 l5 hs hde (by omega) hptr hcurrent hframes hi hmodel
    iframe HC Hc HR
  iunfold Post.wand
  simp only [phasePost]
  isplit
  · iintro %vs' %fr' ⟨%comma, H⟩
    iunfold memberExit at H
    icases H with ⟨%j, %M, %f, %fs, %os, %l3', %l4', %l6', %l7', %l5',
      %⟨hvs, hfr, hf, hfs, hj, hpops, hnext, hl3⟩, Hc, HR⟩
    subst hvs; subst hfr
    iunfold resources at HR
    icases HR with ⟨H32, Hst, Hrd, HX⟩
    iunfold caller at HX
    icases HX with ⟨Hg, H128, He, Hhex, HF⟩
    simp only [Post.mseq_normal]
    iapply mwpi_wand
    isplitl [Hc H32 Hst Hrd Hg H128 He Hhex HF]
    · iapply SerdeIgnMemberBudget.next_funded_weighted cfg lim d inst mi A n g ta hm hd Cg (3 * cfg.regularOpCost + R)
        gt de s ptr cap l3' l4' l6' l7' l5' f maxP F M j fs bs r os
        (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap fs ∗ Fr))
        hstack (by omega) hlen hptr hj hf hnext
      iframe HC Hg H128 Hrd He Hhex H32 Hst HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iunfold Post.wand
    isplit
    · iintro %vs'' %fr'' H; iexfalso; iexact H
    isplit
    · iintro %k %vs'' %fr'' ⟨%j', %l5'', %l6'', %⟨hjj, hjQ, hval, hk, hvs, hfr⟩, Hc, Hg, H128, Hrd, He, Hhex, H32, Hst, HF⟩
      subst hk; subst hvs; subst hfr
      simp only [suffixPost]
      ileft
      isplitr
      · ipureintro; trivial
      iunfold valueExit
      iexists j', M, f, fs, os, l6'', l7', l5''
      isplitr
      · ipureintro; exact ⟨rfl, rfl, hf, hfs, by omega, hpops, hval⟩
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro
        simp only [Nat.add_mul, Nat.sub_sub]
        omega
      iunfold resources
      iunfold caller
      iframe H32 Hst Hrd Hg H128 He Hhex HF
    isplit
    · iintro %vs'' %fr'' H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  isplit
  · iintro %k %vs' %fr' ⟨%hk, H⟩
    subst hk
    simp only [Post.mseq_br, suffixPost]
    iright
    isplitr
    · ipureintro; trivial
    iexact H
  isplit
  · iintro %vs' %fr' H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- The suffix contract is connected by checked equality to the deployed function body. -/
theorem decoded_suffix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (i N : Nat) (opened : Bool) (current : UInt8) (l4 l6 l7 : UInt32) (l5 : UInt64)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hstack : 128 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hcurrent : Br current) (hframes : ∀ f ∈ frames, Br f) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened current else .cont current) frames (bs.drop i) = some (r, ops)) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg (2 * cfg.regularOpCost +
        (SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      resources n s de ptr p cap maxP hl F live bs i frames (caller n g gt s Fr) ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 current.toUInt32) [] ((SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).drop 3)
      (suffixPost cfg inst mi n g Cg R gt s de ptr p cap maxP hl F live frames bs r ops Fr) := by
  rw [suffixCode_at]
  exact suffix cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap maxP hl F live frames bs r ops Fr
    i N opened current l4 l6 l7 l5 hs hstack hde hlen hptr hcurrent hframes hi hmodel

end Proof
end WNear.Binary.SerdeIgnWeightedLoop

namespace WNear.Binary.SerdeIgnValueEntry
open WNear.Binary.SerdeIgnMachineStack
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem opening_entry128_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 l7 : UInt32) (l5 : UInt64)
    (opened : UInt8) (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i q : Nat) (Fr : IProp GF) (hopen : Br opened)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some opened)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames
      (bs.drop i) = some (r, ops)) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnWeightedBudget.regular cfg (if frames.length = 0 then 109 else 64)
          (bs.length - r.length - i) frames.length (SerdeIgnTrace.pushCount ops) + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (flag frames) l4 l5 l6 l7 (current fallback frames)) [] SerdeIgnOpening.entryCode
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = saveOps frames ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.opened opened) frames (bs.drop (q + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' +
            (6 * cfg.regularOpCost + SerdeIgnWeightedBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
              (bs.length - r.length - (q + 1)) (frames.length + 1) (SerdeIgnTrace.pushCount ops') + R)) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some opened)) opened.toUInt32 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hfixed : (if frames.length = 0 then 109 else 60) ≤ (if frames.length = 0 then 109 else 64) := by split <;> omega
  have hreg : SerdeIgnWeightedBudget.regular cfg (if frames.length = 0 then 109 else 60)
      (bs.length - r.length - i) frames.length (SerdeIgnTrace.pushCount ops) ≤
      SerdeIgnWeightedBudget.regular cfg (if frames.length = 0 then 109 else 64) (bs.length - r.length - i) frames.length (SerdeIgnTrace.pushCount ops) := by
    unfold SerdeIgnWeightedBudget.regular
    apply Nat.mul_le_mul_right
    omega
  iintro ⟨#HC, Hc, Hg, H128, Hvt, Hst, Hrd, HF⟩
  iunfold SerdeIgnMember.code at HC
  icases HC with ⟨#CS, -⟩
  icases VecFromElem.stk_split n (s.toNat - 128) 48 80 $$ H128 with ⟨H48, H80⟩
  rw [show s.toNat - 128 + 48 = s.toNat - 80 by omega]
  iapply mwpi_wand
  isplitl [Hc Hg H48 H80 Hvt Hst Hrd HF]
  · iapply SerdeIgnOpening.entry_funded_weighted cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap idx fallback l4 l6 l7 l5
      opened maxP hl F N live frames bs r ops i q (iprop(stk n (s.toNat - 128) 48 ∗ Fr))
      hopen (by omega) hde hcap hlen hptr hi hq hb hframes hr hmodel
    iframe CS Hg H80 Hvt Hst Hrd H48 HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact Nat.add_le_add_right (Nat.add_le_add_right hreg _) _
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨%ops', %hp, Hc, %hfr, %p', %hl', %hhl, Hg, H80, Hvt, Hst, Hrd, H48, HF⟩
    iexists ops'
    iframe Hc
    isplitr
    · ipureintro; exact hp
    isplitr
    · ipureintro; exact hfr
    iexists p', hl'
    isplitr
    · ipureintro; exact hhl
    iframe Hg Hvt Hst Hrd HF
    ihave H128 := VecFromElem.stk_join n (s.toNat - 128) 48 80 $$ [H48 H80]
    · rw [show s.toNat - 128 + 48 = s.toNat - 80 by omega]
      iframe H48 H80
    iexact H128
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

end WNear.Binary.SerdeIgnValueEntry

namespace WNear.Binary.SerdeIgnWeightedExecution
open Wasm Wasm.Near

/-- Future room only along the exact remaining operation trace and actual heap transitions. -/
def Room (maxP : Nat) (hl : Nat) (cap : UInt32) (len : Nat) : List SerdeIgnTrace.Op → Prop
  | [] => True
  | false :: ops => Room maxP hl cap (len - 1) ops
  | true :: ops => ScratchGrow.roomRes hl maxP cap (UInt32.ofNat len) 1 ∧
      ∀ hl', ScratchGrow.hlAfter hl hl' cap (UInt32.ofNat len) 1 →
        Room maxP hl' (SerdeIgnTrace.nextCap cap len true) (len + 1) ops

theorem room_prefix (maxP hl : Nat) (cap : UInt32) (count len : Nat) (ops : List SerdeIgnTrace.Op)
    (h : Room maxP hl cap (count + len) (List.replicate count false ++ ops)) :
    Room maxP hl cap len ops := by
  induction count with
  | zero => simpa only [Nat.zero_add, List.replicate_zero, List.nil_append] using h
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, Room] at h
    have he : count + 1 + len - 1 = count + len := by omega
    rw [he] at h
    exact ih h

theorem room_pops (maxP hl : Nat) (cap : UInt32) (initial frames : List UInt8) (original ops : List SerdeIgnTrace.Op)
    (hp : SerdeIgnWeightedLoop.Pops initial frames original ops) (hr : Room maxP hl cap initial.length original) :
    Room maxP hl cap frames.length ops := by
  obtain ⟨popped, rfl, rfl⟩ := hp
  simp only [List.length_append] at hr
  exact room_prefix maxP hl cap popped.length frames.length ops hr

theorem valid_prefix (cap : UInt32) (count len : Nat) (ops : List SerdeIgnTrace.Op)
    (hv : SerdeIgnTrace.Valid cap (count + len) (List.replicate count false ++ ops)) :
    SerdeIgnTrace.Valid cap len ops := by
  induction count with
  | zero => simpa only [Nat.zero_add, List.replicate_zero, List.nil_append] using hv
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, SerdeIgnTrace.Valid] at hv
    obtain ⟨_, _, _, hv⟩ := hv
    simp only [SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen, Bool.false_eq_true, ite_false] at hv
    have he : count + 1 + len - 1 = count + len := by omega
    rw [he] at hv
    exact ih hv

theorem valid_pops (cap : UInt32) (initial frames : List UInt8) (original ops : List SerdeIgnTrace.Op)
    (hp : SerdeIgnWeightedLoop.Pops initial frames original ops) (hv : SerdeIgnTrace.Valid cap initial.length original) :
    SerdeIgnTrace.Valid cap frames.length ops := by
  obtain ⟨popped, rfl, rfl⟩ := hp
  simp only [List.length_append] at hv
  exact valid_prefix cap popped.length frames.length ops hv

theorem endState_prefix (cap : UInt32) (count len : Nat) (ops : List SerdeIgnTrace.Op) :
    SerdeIgnTrace.endState cap (count + len) (List.replicate count false ++ ops) =
      SerdeIgnTrace.endState cap len ops := by
  induction count with
  | zero => simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, SerdeIgnTrace.endState,
      SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen, Bool.false_eq_true, ite_false]
    have he : count + 1 + len - 1 = count + len := by omega
    rw [he]
    exact ih

theorem endFree_prefix (F : Nat) (cap : UInt32) (count len : Nat) (ops : List SerdeIgnTrace.Op) :
    SerdeIgnTrace.endFreeBound F cap (count + len) (List.replicate count false ++ ops) =
      SerdeIgnTrace.endFreeBound F cap len ops := by
  induction count with
  | zero => simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, SerdeIgnTrace.endFreeBound,
      SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen, SerdeIgnTrace.grows, Bool.false_and, Bool.false_eq_true, ite_false]
    have he : count + 1 + len - 1 = count + len := by omega
    rw [he]
    exact ih

open SerdeIgnMachineStack

theorem endState_pops (cap : UInt32) (initial frames : List UInt8) (original ops : List SerdeIgnTrace.Op)
    (hp : SerdeIgnWeightedLoop.Pops initial frames original ops) :
    SerdeIgnTrace.endState cap initial.length original = SerdeIgnTrace.endState cap frames.length ops := by
  obtain ⟨popped, rfl, rfl⟩ := hp
  simpa only [List.length_append] using endState_prefix cap popped.length frames.length ops

theorem endFree_pops (F : Nat) (cap : UInt32) (initial frames : List UInt8) (original ops : List SerdeIgnTrace.Op)
    (hp : SerdeIgnWeightedLoop.Pops initial frames original ops) :
    SerdeIgnTrace.endFreeBound F cap initial.length original = SerdeIgnTrace.endFreeBound F cap frames.length ops := by
  obtain ⟨popped, rfl, rfl⟩ := hp
  simpa only [List.length_append] using endFree_prefix F cap popped.length frames.length ops

theorem valid_cap (cap : UInt32) (len : Nat) (ops : List SerdeIgnTrace.Op)
    (hv : SerdeIgnTrace.Valid cap len ops) : len ≤ cap.toNat ∧ cap.toNat < 2 ^ 27 := by
  cases ops with
  | nil => exact hv
  | cons op ops => exact ⟨hv.1, hv.2.1⟩

theorem valid_save (cap : UInt32) (frames : List UInt8) (ops : List SerdeIgnTrace.Op)
    (hv : SerdeIgnTrace.Valid cap (physical .val frames).length (saveOps frames ops)) :
    SerdeIgnTrace.Valid (saveCap cap frames) frames.length ops := by
  cases frames with
  | nil => exact hv
  | cons f frames =>
    simp only [physical, List.tail_cons, saveOps, SerdeIgnTrace.Valid] at hv
    simpa only [saveCap, SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen, ite_true, List.length_cons] using hv.2.2.2

theorem room_save_request (maxP hl : Nat) (cap : UInt32) (frames : List UInt8) (ops : List SerdeIgnTrace.Op)
    (hr : Room maxP hl cap (physical .val frames).length (saveOps frames ops)) (hne : frames ≠ []) :
    ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1 := by
  cases frames with
  | nil => exact (hne rfl).elim
  | cons f frames => exact hr.1

theorem room_save (maxP hl hl' : Nat) (cap : UInt32) (frames : List UInt8) (ops : List SerdeIgnTrace.Op)
    (hr : Room maxP hl cap (physical .val frames).length (saveOps frames ops))
    (hh : saveHL hl hl' cap frames) : Room maxP hl' (saveCap cap frames) frames.length ops := by
  cases frames with
  | nil =>
    simp only [saveHL] at hh
    subst hl'
    exact hr
  | cons f frames =>
    simpa only [physical, List.tail_cons, saveCap, SerdeIgnTrace.nextCap, ite_true, List.length_cons] using hr.2 hl' hh

theorem endState_save (cap : UInt32) (frames : List UInt8) (ops : List SerdeIgnTrace.Op) :
    SerdeIgnTrace.endState cap (physical .val frames).length (saveOps frames ops) =
      SerdeIgnTrace.endState (saveCap cap frames) frames.length ops := by
  cases frames with
  | nil => rfl
  | cons f frames =>
    simp only [physical, List.tail_cons, saveOps, SerdeIgnTrace.endState,
      SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen, saveCap, ite_true, List.length_cons]

theorem endFree_save (F : Nat) (cap : UInt32) (frames : List UInt8) (ops : List SerdeIgnTrace.Op) :
    SerdeIgnTrace.endFreeBound F cap (physical .val frames).length (saveOps frames ops) =
      SerdeIgnTrace.endFreeBound (saveF F cap frames) (saveCap cap frames) frames.length ops := by
  cases frames with
  | nil => rfl
  | cons f frames =>
    simp only [physical, List.tail_cons, saveOps, SerdeIgnTrace.endFreeBound,
      SerdeIgnTrace.nextCap, SerdeIgnTrace.nextLen, saveCap, saveF_trace, ite_true, List.length_cons]

end WNear.Binary.SerdeIgnWeightedExecution

namespace WNear.Binary.SerdeIgnWeightedExecution
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnMachineStack

/-- Exact heap lengths permitted by the actual reserve transitions; pops never change memory length. -/
def HeapTrace (hl : Nat) (cap : UInt32) (len : Nat) : List SerdeIgnTrace.Op → Nat → Prop
  | [], final => final = hl
  | false :: ops, final => HeapTrace hl cap (len - 1) ops final
  | true :: ops, final => ∃ next, ScratchGrow.hlAfter hl next cap (UInt32.ofNat len) 1 ∧
      HeapTrace next (SerdeIgnTrace.nextCap cap len true) (len + 1) ops final

theorem heap_prefix (hl : Nat) (cap : UInt32) (count len : Nat) (ops : List SerdeIgnTrace.Op) (final : Nat) :
    HeapTrace hl cap (count + len) (List.replicate count false ++ ops) final ↔ HeapTrace hl cap len ops final := by
  induction count with
  | zero => simp only [Nat.zero_add, List.replicate_zero, List.nil_append]
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, HeapTrace]
    have he : count + 1 + len - 1 = count + len := by omega
    rw [he]
    exact ih

theorem heap_pops (hl : Nat) (cap : UInt32) (initial frames : List UInt8) (original ops : List SerdeIgnTrace.Op)
    (hp : SerdeIgnWeightedLoop.Pops initial frames original ops) (final : Nat) :
    HeapTrace hl cap initial.length original final ↔ HeapTrace hl cap frames.length ops final := by
  obtain ⟨popped, rfl, rfl⟩ := hp
  simpa only [List.length_append] using heap_prefix hl cap popped.length frames.length ops final

theorem heap_save (hl hl' : Nat) (cap : UInt32) (frames : List UInt8) (ops : List SerdeIgnTrace.Op) (final : Nat)
    (hh : saveHL hl hl' cap frames)
    (ht : HeapTrace hl' (saveCap cap frames) frames.length ops final) :
    HeapTrace hl cap (physical .val frames).length (saveOps frames ops) final := by
  cases frames with
  | nil =>
    simp only [saveHL] at hh
    subst hl'
    exact ht
  | cons f fs =>
    refine ⟨hl', hh, ?_⟩
    simpa only [physical, List.tail_cons, saveCap, SerdeIgnTrace.nextCap, ite_true, List.length_cons] using ht

noncomputable def bodyCode : List Instr := SerdeIgnOpening.entryCode ++ SerdeIgnWeightedLoop.suffixCode

theorem bodyCode_at : SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0] = bodyCode := by rfl

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def fullResources (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s de ptr idx : UInt32)
    (maxP : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i : Nat) (frames : List UInt8)
    (p cap : UInt32) (F hl : Nat) (Fr : IProp GF) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ stk n s.toNat 32 ∗
    AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗
    rd n de ptr bs i ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)

def valueInvariant (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n g ta Cg R : Nat) (A : Nat → Nat)
    (gt : GlobalType) (s de ptr idx finalCap : UInt32) (finalF maxP : Nat) (live : List (Nat × Nat))
    (bs r : List UInt8) (Fr : IProp GF) (H : Nat → Prop) (vs : List Value) (fr : Frame) : IProp GF :=
  iprop(∃ (i N : Nat) (frames : List UInt8) (ops : List SerdeIgnTrace.Op) (p cap : UInt32) (F hl : Nat)
      (fallback l6 l7 : UInt32) (l5 : UInt64),
    ⌜vs = [] ∧ fr = fr81 inst mi de s (flag frames) (if frames = [] then 1 else 0) l5 l6 l7 (current fallback frames) ∧
      (∀ f ∈ frames, Br f) ∧ i ≤ bs.length ∧
      SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val frames (bs.drop i) = some (r, ops) ∧
      SerdeIgnTrace.Valid cap (physical .val frames).length ops ∧ Room maxP hl cap (physical .val frames).length ops ∧
      SerdeIgnTrace.endState cap (physical .val frames).length ops = (finalCap, 0) ∧
      SerdeIgnTrace.endFreeBound F cap (physical .val frames).length ops = finalF ∧
      (∀ out, HeapTrace hl cap (physical .val frames).length ops out → H out)⌝ ∗
    credits Cg (SerdeIgnWeightedBudget.regular cfg (if frames.length = 0 then 109 else 64)
      (bs.length - r.length - i) frames.length (SerdeIgnTrace.pushCount ops) + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
    fullResources n g ta A gt s de ptr idx maxP live bs i (physical .val frames) p cap F hl Fr)

def loopPost (cfg : WasmConfig) (inst : Nat) (mi : ModuleInst) (n g ta Cg R : Nat) (A : Nat → Nat)
    (gt : GlobalType) (s de ptr idx finalCap : UInt32) (finalF maxP : Nat) (live : List (Nat × Nat))
    (bs r : List UInt8) (Fr : IProp GF) (H : Nat → Prop) : Post NearState GF :=
  { normal := fun _ _ => iprop(False)
    br := fun k vs fr => iprop(∃ (p : UInt32) (hl : Nat) (l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64),
      ⌜k = 1 ∧ vs = [] ∧ fr = fr81 inst mi de s l3 l4 l5 l6 l7 l8 ∧ H hl⌝ ∗
      credits Cg (8 * cfg.regularOpCost + R) ∗
      fullResources n g ta A gt s de ptr idx maxP live bs (bs.length - r.length) [] p finalCap finalF hl Fr) }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Every checked suffix exit preserves the final allocator coordinates and future room of the outer loop. -/
theorem continue_suffix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx finalCap : UInt32) (maxP hl F finalF : Nat)
    (live : List (Nat × Nat)) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF) (H : Nat → Prop)
    (i N : Nat) (opened : Bool) (f : UInt8) (l4 l6 l7 : UInt32) (l5 : UInt64)
    (hs : 128 ≤ s.toNat) (hs32 : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hf : Br f) (hframes : ∀ f ∈ frames, Br f) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened f else .cont f) frames (bs.drop i) = some (r, ops))
    (hvalid : SerdeIgnTrace.Valid cap frames.length ops) (hroom : Room maxP hl cap frames.length ops)
    (hend : SerdeIgnTrace.endState cap frames.length ops = (finalCap, 0))
    (hfree : SerdeIgnTrace.endFreeBound F cap frames.length ops = finalF)
    (hheap : ∀ out, HeapTrace hl cap frames.length ops out → H out) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg (2 * cfg.regularOpCost +
        (SerdeIgnWeightedBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance f else 0)
          (bs.length - r.length - i) (frames.length + 1) (SerdeIgnTrace.pushCount ops) + SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      fullResources n g ta A gt s de ptr idx maxP live bs i frames p cap F hl Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 f.toUInt32) [] SerdeIgnWeightedLoop.suffixCode
      (Post.mloop cfg Cg 0 []
        (valueInvariant cfg inst mi n g ta Cg R A gt s de ptr idx finalCap finalF maxP live bs r Fr H)
        (loopPost cfg inst mi n g ta Cg R A gt s de ptr idx finalCap finalF maxP live bs r Fr H)) := by
  iintro ⟨#HC, Hc, HR⟩
  iunfold fullResources at HR
  icases HR with ⟨Hg, H128, H32, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF]
  · iapply SerdeIgnWeightedLoop.suffix cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap maxP hl F live frames bs r ops
      (iprop(AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      i N opened f l4 l6 l7 l5 hs32 hs hde hlen hptr hf hframes hi hmodel
    iframe HC Hc
    iunfold SerdeIgnWeightedLoop.resources
    iunfold SerdeIgnWeightedLoop.caller
    iframe H32 Hst Hrd Hg H128 He Hhex Hvt Hid HF
  iunfold Post.wand
  simp only [SerdeIgnWeightedLoop.suffixPost]
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H
    icases H with (H | H)
    · icases H with ⟨%hk, H⟩
      subst hk
      iunfold SerdeIgnWeightedLoop.valueExit at H
      icases H with ⟨%j, %M, %cur, %fs, %os, %l6', %l7', %l5',
        %⟨hvs, hfr, hcur, hfs, hj, hpops, hnext⟩, Hc, HR⟩
      subst hvs; subst hfr
      cases M with
      | zero => simp only [SerdeIgnMachineTrace.run] at hnext; cases hnext
      | succ M =>
        have hv' := valid_pops cap frames fs ops os hpops hvalid
        have hr' := room_pops maxP hl cap frames fs ops os hpops hroom
        have he' := (endState_pops cap frames fs ops os hpops).symm.trans hend
        have hf' := (endFree_pops F cap frames fs ops os hpops).symm.trans hfree
        simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
        isplitr
        · ipureintro; omega
        mpay with skip
        iunfold valueInvariant
        iexists j, M, cur :: fs, os, p, cap, F, hl, cur.toUInt32, l6', l7', l5'
        isplitr
        · ipureintro
          refine ⟨rfl, rfl, ?_, hj, hnext, hv', hr', he', hf', ?_⟩
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hcur
          · exact hfs f hf
          · intro out hh
            exact hheap out ((heap_pops hl cap frames fs ops os hpops out).mpr hh)
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro
          simp only [List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero, _root_.and_false, ite_false,
            physical, List.tail_cons, Nat.add_mul, Nat.sub_sub]
          omega
        iunfold SerdeIgnWeightedLoop.resources at HR
        icases HR with ⟨H32, Hst, Hrd, HX⟩
        iunfold SerdeIgnWeightedLoop.caller at HX
        icases HX with ⟨Hg, H128, He, Hhex, Hvt, Hid, HF⟩
        iunfold fullResources
        simp only [physical, List.tail_cons]
        iframe Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF
    · icases H with ⟨%hk, H⟩
      subst hk
      iunfold SerdeIgnWeightedLoop.successExit at H
      icases H with ⟨%j, %l3', %l4', %l6', %l7', %l8', %l5', %⟨hvs, hfr, hj, hjle, hpops⟩, Hc, HR⟩
      have he' := (endState_pops cap frames [] ops [] hpops).symm.trans hend
      have hf' := (endFree_pops F cap frames [] ops [] hpops).symm.trans hfree
      simp only [List.length_nil, SerdeIgnTrace.endState, Prod.mk.injEq] at he'
      simp only [List.length_nil, SerdeIgnTrace.endFreeBound] at hf'
      have hH : H hl := hheap hl ((heap_pops hl cap frames [] ops [] hpops hl).mpr rfl)
      obtain ⟨hcap, -⟩ := he'
      subst finalCap; subst finalF; subst j; subst hvs; subst hfr
      simp only [Post.mloop, List.nil_append, loopPost]
      iexists p, hl, l3', l4', l6', l7', l8', l5'
      isplitr
      · ipureintro; exact ⟨by trivial, by trivial, by trivial, hH⟩
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iunfold SerdeIgnWeightedLoop.resources at HR
      icases HR with ⟨H32, Hst, Hrd, HX⟩
      iunfold SerdeIgnWeightedLoop.caller at HX
      icases HX with ⟨Hg, H128, He, Hhex, Hvt, Hid, HF⟩
      iunfold fullResources
      rw [← hf']
      iframe Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The complete actual value-loop iteration preserves the exact allocator endpoint and remaining trace. -/
theorem value_iteration (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr idx finalCap : UInt32) (finalF maxP : Nat)
    (live : List (Nat × Nat)) (bs r : List UInt8) (Fr : IProp GF) (H : Nat → Prop)
    (hs : 128 ≤ s.toNat) (hs32 : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (vs : List Value) (fr : Frame) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      valueInvariant cfg inst mi n g ta Cg R A gt s de ptr idx finalCap finalF maxP live bs r Fr H vs fr ⊢
    mwpi cfg lim d fr vs bodyCode
      (Post.mloop cfg Cg 0 []
        (valueInvariant cfg inst mi n g ta Cg R A gt s de ptr idx finalCap finalF maxP live bs r Fr H)
        (loopPost cfg inst mi n g ta Cg R A gt s de ptr idx finalCap finalF maxP live bs r Fr H)) := by
  iintro ⟨#HC, HI⟩
  iunfold valueInvariant at HI
  icases HI with ⟨%i, %N, %frames, %ops, %p, %cap, %F, %hl, %fallback, %l6, %l7, %l5,
    %⟨hvs, hfr, hframes, hi, hmodel, hvalid, hroom, hend, hfree, hheap⟩, Hc, HR⟩
  subst hvs; subst hfr
  obtain ⟨b, t, hskip⟩ : ∃ b t, NearInterface.Json.skipWhitespace (bs.drop i) = b :: t := by
    cases hsk : NearInterface.Json.skipWhitespace (bs.drop i) with
    | nil =>
      simp only [SerdeIgnMachineTrace.run, hsk, SerdeIgnPure.vSkip_nil, Option.bind_none] at hmodel
      cases hmodel
    | cons b t => exact ⟨b, t, rfl⟩
  let q := i + wsLen (bs.drop i)
  have hdr : NearInterface.Json.skipWhitespace (bs.drop i) = bs.drop q := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
  have hb : bs[q]? = some b := (SerdeStructLoop.drop_cons (hdr.symm.trans hskip)).1
  have hq := SerdeNextKey.getElem_lt hb
  have hws : NearInterface.Json.isWhitespace b = false :=
    SerdeRead.wsLen_stop (bs.drop i) b (by simpa only [List.getElem?_drop] using hb)
  by_cases hopen : Br b
  · have hsave := SerdeIgnOpening.opening_step N frames (bs.drop i) r ops b t hopen hskip hmodel
    obtain ⟨ops0, _, hops0⟩ := SerdeIgnSegments.save_some hsave
    have hv0 := hops0 ▸ hvalid
    have hr0 := hops0 ▸ hroom
    have hcap : cap.toNat < 2 ^ 27 := (valid_cap cap _ _ hvalid).2
    have hframeslim : (physical .val frames).length + 1 < 2 ^ 27 := by
      cases frames with
      | nil => simp [physical]
      | cons f fs => exact hv0.2.2.1
    have hreq : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1 :=
      fun hne => room_save_request maxP hl cap frames ops0 hr0 hne
    iunfold fullResources at HR
    icases HR with ⟨Hg, H128, H32, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
    unfold bodyCode
    iapply mwpi_seq
    iapply mwpi_wand
    isplitl [Hc Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF]
    · iapply SerdeIgnValueEntry.opening_entry128_weighted cfg lim d inst mi A n g ta hm (by omega) Cg R
        gt s de ptr p cap idx fallback (if frames = [] then 1 else 0) l6 l7 l5 b maxP hl F N live frames bs r ops i q
        (iprop(stk n s.toNat 32 ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
        hopen hs hde hcap (by omega) hptr hi rfl hb hframeslim hreq hmodel
      iframe HC Hc Hg H128 Hvt Hst Hrd H32 He Hhex Hid HF
    iunfold Post.wand
    isplit
    · iintro %vs' %fr' ⟨%os, %⟨hops, hsub⟩, Hc, %⟨hvs', hfr'⟩, %p', %hl', %hhl,
        Hg, H128, Hvt, Hst, Hrd, H32, He, Hhex, Hid, HF⟩
      subst hvs'; subst hfr'
      cases N with
      | zero => simp only [SerdeIgnMachineTrace.run] at hsub; cases hsub
      | succ N =>
        have hv' := valid_save cap frames os (hops ▸ hvalid)
        have hr' := room_save maxP hl hl' cap frames os (hops ▸ hroom) hhl
        have he' := (endState_save cap frames os).symm.trans (hops ▸ hend)
        have hf' := (endFree_save F cap frames os).symm.trans (hops ▸ hfree)
        simp only [Post.mseq_normal]
        have hnextspec := continue_suffix cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p' (saveCap cap frames) idx finalCap
          maxP hl' (saveF F cap frames) finalF live frames bs r os Fr H (q + 1) N true b
          (if frames = [] then 1 else 0) b.toUInt32 b.toUInt32 (optByte (some b))
          hs hs32 hde hlen hptr hopen hframes (by omega) hsub hv' hr' he' hf'
          (fun out hh => hheap out (hops ▸ heap_save hl hl' cap frames os out hhl hh))
        simp only [ite_true] at hnextspec
        iapply hnextspec
        iunfold fullResources
        simp only [physical]
        iframe HC Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro
        simp only [ite_true, Nat.add_mul, Nat.sub_sub]
        omega
    isplit
    · iintro %k %vs' %fr' H; iexfalso; iexact H
    isplit
    · iintro %vs' %fr' H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  · have hb5B : b ≠ 0x5B := fun h => hopen (Or.inl h)
    have hb7B : b ≠ 0x7B := fun h => hopen (Or.inr h)
    cases frames with
    | nil =>
      have hops := (SerdeIgnValueEntry.top_indices N bs r ops i q b rfl hb hb5B hb7B hmodel).2.2
      subst ops
      simp only [physical, List.tail_nil, List.length_nil, SerdeIgnTrace.endState, Prod.mk.injEq] at hend
      simp only [physical, List.tail_nil, List.length_nil, SerdeIgnTrace.endFreeBound] at hfree
      obtain ⟨hcap, -⟩ := hend
      subst finalCap; subst finalF
      simp only [flag, current, ite_true]
      iunfold fullResources at HR
      icases HR with ⟨Hg, H128, H32, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
      simp only [physical, List.tail_nil, List.tail_cons]
      unfold bodyCode
      iapply mwpi_seq
      iapply mwpi_wand
      isplitl [Hc Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF]
      · iapply SerdeIgnValueEntry.top_entry cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr p cap 0 l6 l7 fallback l5
          bs r [] i q maxP hl F N live b (iprop(AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ Fr))
          hs hs32 hde hlen hptr hi rfl hb hws hb5B hb7B hmodel
        iframe HC Hg H128 H32 Hst Hrd He Hhex Hid Hvt HF
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro
        simp only [SerdeIgnWeightedBudget.regular, SerdeIgnTrace.extraCost, SerdeIgnTrace.pushCount, physical, List.tail_nil,
          List.length_nil, ite_true, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
        omega
      iunfold Post.wand
      isplit
      · iintro %vs' %fr' H; iexfalso; iexact H
      isplit
      · iintro %k %vs' %fr' ⟨%⟨_, hk⟩, Hc, %⟨hvs', hfr'⟩, H32, Hst, Hg, H128, Hrd, He, Hhex, Hid, Hvt, HF⟩
        subst hk; subst hvs'; subst hfr'
        simp only [Post.mseq_br, Post.mloop, List.nil_append, loopPost]
        iexists p, hl, 1, 1, 0, b.toUInt32, fallback, optByte (some b)
        iframe Hc
        isplitr
        · ipureintro; exact ⟨by trivial, by trivial, by trivial, hheap hl rfl⟩
        iunfold fullResources
        iframe Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF
      isplit
      · iintro %vs' %fr' H; iexfalso; iexact H
      · iintro H; iexfalso; iexact H
    | cons f fs =>
      have hf := hframes f (by simp)
      have hfs : ∀ f ∈ fs, Br f := fun f h => hframes f (by simp [h])
      simp only [physical, List.tail_cons] at hvalid hroom hend hfree
      simp only [flag, current, List.cons_ne_nil, ite_false]
      iunfold fullResources at HR
      icases HR with ⟨Hg, H128, H32, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
      simp only [physical, List.tail_nil, List.tail_cons]
      unfold bodyCode
      iapply mwpi_seq
      iapply mwpi_wand
      isplitl [Hc Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF]
      · iapply SerdeIgnValueEntry.pending_entry_weighted cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr cap l6 l7 l5
          bs r fs ops i q maxP F N b f
          (iprop(stk n s.toNat 32 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
            SerdeIgnStack.state n maxP hl live F (de + 12) p cap fs ∗ Fr))
          hs (by omega) hlen hptr hi rfl hb hws hb5B hb7B hmodel
        iframe HC Hg H128 Hrd He Hhex Hid H32 Hvt Hst HF
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro
        simp only [physical, List.tail_cons, List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          _root_.and_false, ite_false]
        omega
      iunfold Post.wand
      isplit
      · iintro %vs' %fr' ⟨%e, %⟨hqe, heQ, hsub⟩, Hc, %⟨hvs', hfr'⟩, Hg, H128, Hrd, He, Hhex, Hid, H32, Hvt, Hst, HF⟩
        subst hvs'; subst hfr'
        cases N with
        | zero => simp only [SerdeIgnMachineTrace.run] at hsub; cases hsub
        | succ N =>
          simp only [Post.mseq_normal]
          have hnextspec := continue_suffix cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap idx finalCap maxP hl F finalF live fs bs r ops Fr H
            e N false f 0 0 b.toUInt32 (optByte (some b)) hs hs32 hde hlen hptr hf hfs (by omega) hsub hvalid hroom hend hfree hheap
          simp only [Bool.false_eq_true, ite_false] at hnextspec
          iapply hnextspec
          iunfold fullResources
          iframe HC Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro
          simp only [Bool.false_eq_true, ite_false, Nat.add_mul, Nat.sub_sub]
          omega
      isplit
      · iintro %k %vs' %fr' H; iexfalso; iexact H
      isplit
      · iintro %vs' %fr' H; iexfalso; iexact H
      · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- The actual outer loop starts with one credit ownership and fixes its final allocation coordinates. -/
theorem value_loop (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF) (i N : Nat)
    (hs : 128 ≤ s.toNat) (hs32 : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val [] (bs.drop i) = some (r, ops))
    (hvalid : SerdeIgnTrace.Valid cap 0 ops) (hroom : Room maxP hl cap 0 ops) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg ((110 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops + R) ∗
      fullResources n g ta A gt s de ptr idx maxP live bs i [] p cap F hl Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 0 1 0 0 0 0) [] [.loop .empty bodyCode]
      (loopPost cfg inst mi n g ta Cg R A gt s de ptr idx (SerdeIgnTrace.endState cap 0 ops).1
        (SerdeIgnTrace.endFreeBound F cap 0 ops) maxP live bs r Fr (HeapTrace hl cap 0 ops)) := by
  have hpush := SerdeIgnWeightedBudget.pushes_le_remaining (N + 1) .val [] bs r ops i hmodel
  have hdiff : 110 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops =
      1 + (109 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) := by omega
  have hmul := congrArg (fun n => n * cfg.regularOpCost) hdiff
  simp only [Nat.add_mul] at hmul
  have hgood := SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
    (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length (N + 1) .val [] (bs.drop i)
  have hlegal := (hgood r ops hmodel).1
  have hzero := SerdeIgnMachineTrace.legal_endLen cap 0 ops hlegal
  have hend : SerdeIgnTrace.endState cap 0 ops = ((SerdeIgnTrace.endState cap 0 ops).1, 0) := by
    apply Prod.ext
    · rfl
    · exact hzero
  iintro ⟨#HC, Hc, HR⟩
  iapply MemCpy.mwpi_loop0 (Cg := Cg)
    (R := SerdeIgnWeightedBudget.regular cfg 109 (bs.length - r.length - i) 0 (SerdeIgnTrace.pushCount ops) + SerdeIgnTrace.extraCost cfg F cap 0 ops + R)
    .empty bodyCode
    (valueInvariant cfg inst mi n g ta Cg R A gt s de ptr idx (SerdeIgnTrace.endState cap 0 ops).1
      (SerdeIgnTrace.endFreeBound F cap 0 ops) maxP live bs r Fr (HeapTrace hl cap 0 ops)) rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iapply value_iteration cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr idx _ _ maxP live bs r Fr (HeapTrace hl cap 0 ops) hs hs32 hde hlen hptr X _
    iframe HC HI
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [SerdeIgnWeightedBudget.regular, Nat.mul_zero, Nat.sub_zero, Nat.add_mul]
    omega
  inext
  iintro Hc
  iunfold valueInvariant
  iexists i, N, [], ops, p, cap, F, hl, 0, 0, 0, 0
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, by simp, hi, hmodel, hvalid, hroom, hend, rfl, fun _ h => h⟩
  simp only [List.length_nil, ite_true, physical, List.tail_nil]
  iframe Hc HR

noncomputable def innerError : List Instr := (SerdeIgnSegments.bodyAt f81.body [14, 0, 0]).drop 1
noncomputable def middleError : List Instr := (SerdeIgnSegments.bodyAt f81.body [14, 0]).drop 1
noncomputable def mainCode : List Instr :=
  [.block .empty ([.block .empty ([.block .empty ([.loop .empty bodyCode] ++ innerError)] ++ middleError)] ++
    SerdeIgnScalarDone.successCode)] ++ SerdeIgnScalarDone.returnCode

theorem body_eq : f81.body = SerdeIgnSegments.startCode ++ mainCode := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The actual three enclosing blocks bypass both retained error tails on loop success. -/
theorem main (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp de ptr p cap idx : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF) (i N : Nat)
    (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val [] (bs.drop i) = some (r, ops))
    (hvalid : SerdeIgnTrace.Valid cap 0 ops) (hroom : Room maxP hl cap 0 ops) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg ((113 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops + R) ∗
      fullResources n g ta A gt (sp - 32) de ptr idx maxP live bs i [] p cap F hl Fr ⊢
    mwpi cfg lim d (fr81 inst mi de (sp - 32) 0 1 0 0 0 0) [] mainCode
      { normal := fun vs _ => iprop(∃ p' hl', credits Cg R ∗ ⌜vs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
          rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  have hpush := SerdeIgnWeightedBudget.pushes_le_remaining (N + 1) .val [] bs r ops i hmodel
  have hdiff : 113 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops =
      3 + (110 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) := by omega
  have hmul := congrArg (fun n => n * cfg.regularOpCost) hdiff
  simp only [Nat.add_mul] at hmul
  have hs : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hs128 : 128 ≤ (sp - 32).toNat := by omega
  have hs32 : (sp - 32).toNat + 32 ≤ 2 ^ 32 := by have := sp.toNat_lt; omega
  iintro ⟨#HC, Hc, HR⟩
  unfold mainCode
  iapply mwpi_seq
  mstep
  iapply mwpi_cons
  mstep
  iapply mwpi_cons
  mstep
  iapply mwpi_cons
  iapply mwpi_wand
  isplitl [Hc HR]
  · iapply value_loop cfg lim d inst mi A n g ta hm hd Cg R gt (sp - 32) de ptr p cap idx maxP hl F live bs r ops Fr i N
      hs128 hs32 hde hlen hptr hi hmodel hvalid hroom
    iframe HC HR
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul, Nat.sub_sub] at hmul ⊢
    omega
  iunfold Post.wand
  simp only [loopPost]
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr ⟨%p', %hl', %l3, %l4, %l6, %l7, %l8, %l5, %⟨hk, hvs, hfr, hheap⟩, Hc, HR⟩
    subst hk; subst hvs; subst hfr
    simp only [Post.mseq_br, Post.mblock_br_succ, Post.mblock_br_zero, List.length_nil, List.drop_nil, List.nil_append]
    isplitr
    · ipureintro; omega
    mpay with skip
    iunfold fullResources at HR
    icases HR with ⟨Hg, H128, H32, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
    unfold SerdeIgnScalarDone.successCode
    simp only [fr81]
    mstep; mstep
    unfold SerdeIgnScalarDone.returnCode
    have hg := hm.glob
    mstep; mstep; mstep
    mstep [Hg]
    rw [show sp - 32 + 32 = sp by simp]
    mstep
    mcredits R
    iexists p', hl'
    iframe Hc Hg Hvt Hst Hrd He Hhex Hid HF
    isplitr
    · ipureintro; exact ⟨by trivial, hheap⟩
    iapply VecFromElem.stk_join n (sp.toNat - 160) 128 32
    rw [show sp.toNat - 160 + 128 = sp.toNat - 32 by omega, hs]
    rw [show sp.toNat - 32 - 128 = sp.toNat - 160 by omega]
    iframe H128 H32
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H


set_option maxRecDepth 100000 in
/-- The real prologue clears an arbitrary old length word; it does not inspect scratch contents. -/
theorem start_raw (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp de p cap sl : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32) :
    SerdeIgnSegments.code (GF := GF) n maxP inst mi A ∗ credits Cg (53 * cfg.regularOpCost + R) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
      SerdeValueState.scratchPre n maxP hl live F de p cap sl ⊢
    mwpi cfg lim d ⟨entryLocals f81 [.i32 de], inst, mi⟩ [] SerdeIgnSegments.startCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de (sp - 32) 0 1 0 0 0 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗ stk n (sp.toNat - 160) 128 ∗ stk n (sp.toNat - 32) 32 ∗
          SerdeIgnStack.state n maxP hl live F (de + 12) p cap []) } := by
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hentry : entryLocals f81 [.i32 de] = #[.i32 de, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i32 0, .i32 0] := rfl
  have key := SerdeDeStr.f343_s (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm
    (by omega) Cg (de + 12) sl (by rw [hd12]; omega)
  iintro ⟨#HC, Hc, Hg, H160, Hst⟩
  iunfold SerdeValueState.scratchPre at Hst
  icases Hst with ⟨D8, D0, D4, Hsb⟩
  iunfold SerdeIgnSegments.code at HC
  icases HC with ⟨#C81, -⟩
  iunfold SerdeIgnValue.code81 at C81
  icases C81 with ⟨#CN, -, #F82, #F674, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, -, -, -, -, -, #Hi⟩
  have hg := hm.glob
  have ha82 := hm.funcs 82 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  unfold SerdeIgnSegments.startCode
  rw [hentry]
  mstep [Hg]
  repeat mstep
  mstep [Hg]
  repeat mstep
  mcall key using [D8]
  · rw [hd12]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    iframe D8
  icases HQ with ⟨%hrs, D8⟩
  subst hrs
  clear key
  repeat mstep
  mcredits R
  iframe Hc Hg
  isplitr
  · ipureintro; trivial
  icases VecFromElem.stk_split n (sp.toNat - 160) 128 32 $$ H160 with ⟨H128, H32⟩
  rw [show sp.toNat - 160 + 128 = sp.toNat - 32 by omega]
  iframe H128 H32
  iunfold SerdeIgnStack.state
  rw [hd12]
  simp only [List.length_nil, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
  iframe D0 D4 D8 Hsb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Full successful function 81: actual prologue, both loops, retained error tails and stack-restoring return. -/
theorem f81_core (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr p cap idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (sl : UInt32) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (i N : Nat) (Fr : IProp GF)
    (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val [] (bs.drop i) = some (r, ops))
    (hvalid : SerdeIgnTrace.Valid cap 0 ops) (hroom : Room maxP hl cap 0 ops) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ⊢ MFunSpec cfg lim d type inst mi f81 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeValueState.scratchPre n maxP hl live F de p cap sl ∗ rd n de ptr bs i ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      (fun _ => (166 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops)
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
  have hpush := SerdeIgnWeightedBudget.pushes_le_remaining (N + 1) .val [] bs r ops i hmodel
  have hdiff : 166 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops =
      53 + (113 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) := by omega
  have hmul := congrArg (fun n => n * cfg.regularOpCost) hdiff
  simp only [Nat.add_mul] at hmul
  have hs : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iintro #HC
  ihave #CS := HC
  iunfold SerdeIgnMember.code at CS
  icases CS with ⟨#CS, -⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, H160, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
  subst args
  rw [body_eq]
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hg H160 Hvt Hst Hrd He Hhex Hid HF]
  · iapply mwpi_frame (R := iprop(AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
    isplitl [Hvt Hrd He Hhex Hid HF]
    · iframe Hvt Hrd He Hhex Hid HF
    iapply start_raw cfg lim d inst mi A n g ta hm (by omega) Cg
      ((113 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops + R)
      gt sp de p cap sl maxP hl F live hsp hde
    iframe CS Hg H160 Hst
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    omega
  iunfold Post.wand
  simp only [Post.frame]
  isplit
  · iintro %vs %fr ⟨⟨Hvt, Hrd, He, Hhex, Hid, HF⟩, Hc, %⟨hvs, hfr⟩, Hg, H128, H32, Hst⟩
    subst hvs; subst hfr
    simp only [Post.mseq_normal]
    iapply mwpi_wand
    isplitl [Hc Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF]
    · iapply main cfg lim d inst mi A n g ta hm hd Cg R gt sp de ptr p cap idx maxP hl F live bs r ops Fr i N
        hsp hde hlen hptr hi hmodel hvalid hroom
      iframe HC Hc
      iunfold fullResources
      rw [hs, show sp.toNat - 32 - 128 = sp.toNat - 160 by omega]
      iframe Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF
    iunfold Post.wand
    isplit
    · iintro %vs %fr ⟨%p', %hl', Hc, %⟨hvs, hheap⟩, Hg, H160, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
      subst vs
      simp only [Post.mfunc, htype, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self, List.drop_zero]
      isplitr
      · ipureintro; omega
      iexists R
      isplitl [Hc]
      · iexact Hc
      iintro Hc
      iframe Hc
      iexists p', hl'
      iframe Hg H160 Hvt Hst Hrd He Hhex Hid HF
      ipureintro; exact ⟨trivial, hheap⟩
    isplit
    · iintro %k %vs %fr H; iexfalso; iexact H
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr ⟨-, H⟩; iexfalso; iexact H
  isplit
  · iintro %vs %fr ⟨-, H⟩; iexfalso; iexact H
  · iintro ⟨-, H⟩; iexfalso; iexact H

set_option maxRecDepth 100000 in
theorem f81_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr p cap idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (sl : UInt32) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (i : Nat) (Fr : IProp GF)
    (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hcap : cap.toNat < 2 ^ 27)
    (htrace : SerdeIgnMachineTrace.trace (bs.drop i) = some (r, ops))
    (hroom : Room maxP hl cap 0 ops) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ⊢ MFunSpec cfg lim d type inst mi f81 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeValueState.scratchPre n maxP hl live F de p cap sl ∗ rd n de ptr bs i ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      (fun _ => (166 + 470 * (bs.length - r.length - i) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops)
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
  have hskip : vSkip (bs.drop i) = some r := by
    rw [← SerdeIgnMachineTrace.erase_trace, htrace]
    rfl
  obtain ⟨os, ht, hv, _, _, _⟩ := SerdeIgnMachineTrace.trace_valid cap hcap (by simp only [List.length_drop]; omega) hskip
  have he : ops = os := by
    have h := htrace.symm.trans ht
    exact (Prod.mk.inj (Option.some.inj h)).2
  rw [← he] at hv
  have hmTrace : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (2 * (bs.drop i).length + 1 + 1)
      .val [] (bs.drop i) = some (r, ops) := by
    simpa only [SerdeIgnMachineTrace.trace, Nat.add_assoc, Nat.reduceAdd] using htrace
  exact f81_core cfg lim d type htype inst mi A n g ta hm hd Cg gt sp de ptr p cap idx maxP hl F live sl bs r ops i
    (2 * (bs.drop i).length + 1) Fr hsp hde (by omega) hptr hi hmTrace hv hroom

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The real colon/ignore call consumes the full reader contract and returns its exact resource endpoints. -/
theorem f201_traced (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp acc de ptr p cap sl idx : UInt32)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (i : Nat) (Fr : IProp GF)
    (hsp : 160 ≤ sp.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32) (hacc : acc.toNat + 4 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hi : i ≤ bs.length)
    (hc : bs[i + wsLen (bs.drop i)]? = some 0x3A) (hcap : cap.toNat < 2 ^ 27)
    (htrace : SerdeIgnMachineTrace.trace (bs.drop (i + wsLen (bs.drop i) + 1)) = some (r, ops))
    (hroom : Room maxP hl cap 0 ops) :
    SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code (GF := GF) n maxP inst mi A ⊢
    MFunSpec cfg lim d types[32]! inst mi f201 Cg
      (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeValueState.scratchPre n maxP hl live F de p cap sl ∗ rd n de ptr bs i ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      (fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
        ((166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1)) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost +
          SerdeIgnTrace.extraCost cfg F cap 0 ops))
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        n ↦[i32][ acc.toNat ] de ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
        AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
  have hcolon := SerdeNextKey.getElem_lt hc
  have key89 := SerdeColonSuccess.f89_colon (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp de ptr bs i (by omega) (by omega) (by omega) hi hc
  have key81 := f81_traced (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp de ptr p cap idx maxP hl F live sl bs r ops (i + wsLen (bs.drop i) + 1) Fr
    hsp hde hlen (by omega) (by omega) hcap htrace hroom
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
  generalize hK : (166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1)) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost +
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

end Proof
end WNear.Binary.SerdeIgnWeightedExecution

namespace WNear.Binary.SerdeIgnWeightedExecution
open Wasm Wasm.Near
theorem room_eq (maxP hl : Nat) (cap : UInt32) (len : Nat) (ops : List SerdeIgnTrace.Op) :
    Room maxP hl cap len ops = SerdeIgnExecution.Room maxP hl cap len ops := by
  induction ops generalizing hl cap len with
  | nil => rfl
  | cons op ops ih => cases op <;> simp only [Room, SerdeIgnExecution.Room, ih]
theorem heapTrace_eq (hl : Nat) (cap : UInt32) (len : Nat) (ops : List SerdeIgnTrace.Op) (final : Nat) :
    HeapTrace hl cap len ops final = SerdeIgnExecution.HeapTrace hl cap len ops final := by
  induction ops generalizing hl cap len with
  | nil => rfl
  | cons op ops ih => cases op <;> simp only [HeapTrace, SerdeIgnExecution.HeapTrace, ih]
end WNear.Binary.SerdeIgnWeightedExecution

namespace WNear.Binary.SerdeIgnExecution
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.VecFromElem
open WNear.Binary.SerdeRead (rd wsLen)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
theorem f201_weighted_v86 (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
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
        ((166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1)) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost +
          SerdeIgnTrace.extraCost cfg F cap 0 ops))
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        n ↦[i32][ acc.toNat ] de ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
        AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n 2048 hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
  have hp := trace_pages_v86 (bs.drop (i + wsLen (bs.drop i) + 1)) r ops cap
    (by simp only [List.length_drop]; omega) hcap htrace
  have hr := room_of_pages 2048 hl cap 0 ops (by decide) hpos halign (by omega)
  rw [← SerdeIgnWeightedExecution.room_eq] at hr
  have ht := SerdeIgnWeightedExecution.f201_traced (GF := GF) cfg lim d inst mi A n g ta hm hd Cg gt
    sp acc de ptr p cap sl idx 2048 hl F live bs r ops i Fr hsp hde hacc (by omega) hptr hi hc hcap htrace hr
  simp_rw [SerdeIgnWeightedExecution.heapTrace_eq] at ht
  exact ht
end WNear.Binary.SerdeIgnExecution
