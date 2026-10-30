import Bridge.Functions.SerdeIgnClosing

/-! # Retaining the depth reserve through actual ignored-container members -/

namespace WNear.Binary.SerdeIgnMemberBudget

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnMember

/-- Sixty-four operations fund the next value entry; one more pays its loop branch. -/
theorem cost_le_entry (cfg : WasmConfig) (i q e j : Nat) (hq : i ≤ q) (he : q + 1 ≤ e) (hj : e ≤ j) :
    SerdeIgnMember.cost cfg i q e j + 65 * cfg.regularOpCost ≤ 470 * (j + 1 - i) * cfg.regularOpCost := by
  have h : 600 + 96 * (q - i) + 300 * (e - (q + 1)) + 96 * (j - e) + 65 ≤ 470 * (j + 1 - i) := by omega
  simpa only [SerdeIgnMember.cost, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

/-- Consumed member bytes pay their work without borrowing the future closing reserve. -/
theorem regular_split (cfg : WasmConfig) (consumed remaining depth : Nat) (hd : depth ≤ remaining) :
    SerdeIgnBudget.regular cfg 0 (consumed + remaining) depth =
      470 * consumed * cfg.regularOpCost + SerdeIgnBudget.regular cfg 0 remaining depth := by
  have hh : 110 * depth ≤ 470 * remaining := by omega
  unfold SerdeIgnBudget.regular
  simp only [Nat.zero_add]
  rw [Nat.mul_add, Nat.add_sub_assoc hh, Nat.add_mul]

/-- The value-entry allowance and its loop-branch payment preserve the same depth reserve. -/
theorem regular_entry (cfg : WasmConfig) (remaining depth : Nat) (hd : depth ≤ remaining) :
    cfg.regularOpCost + SerdeIgnBudget.regular cfg 64 remaining depth =
      65 * cfg.regularOpCost + SerdeIgnBudget.regular cfg 0 remaining depth := by
  have h0 := SerdeIgnBudget.regular_reserve cfg 0 remaining depth hd
  have h64 := SerdeIgnBudget.regular_reserve cfg 64 remaining depth hd
  simp only [Nat.zero_add, Nat.add_mul] at h0 h64
  omega

/-- A successful complete next-member transition retains enough input for every active frame. -/
theorem next_depth (N : Nat) (f : UInt8) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (i : Nat) (hf : Br f) (hi : i ≤ bs.length)
    (h : nextModel N f frames (bs.drop i) = some (r, ops)) :
    frames.length + 1 ≤ bs.length - r.length - i := by
  rcases hf with rfl | rfl
  · simp only [nextModel, ite_true] at h
    simpa only [SerdeIgnBudget.active, List.length_cons] using
      SerdeIgnBudget.active_le_remaining N .val (0x5B :: frames) bs r ops i h
  · simp only [nextModel, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at h
    obtain ⟨q, e, j, key, rest, hq, he, hj, hquote, hcolon, hkey, hqe, hnext⟩ := key_indices bs i _ _ hi h
    have hp := SerdeIgnBudget.active_le_remaining N .val (0x7B :: frames) bs r ops (j + 1) hnext
    simp only [SerdeIgnBudget.active, List.length_cons] at hp
    omega

/-- The complete opened phase selects its first member without consuming the first byte. -/
theorem first_next (N : Nat) (f c : UInt8) (frames bs t r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (hf : Br f) (hs : NearInterface.Json.skipWhitespace bs = c :: t)
    (h93 : c ≠ 0x5D) (h125 : c ≠ 0x7D)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) (.opened f) frames bs = some (r, ops)) :
    nextModel N f frames (c :: t) = some (r, ops) := by
  rcases SerdeIgnContainer.phase_cases N true f c frames bs t r ops hf hs h with
    ⟨he, -⟩ | ⟨-, -, -, -, hn⟩ | ⟨he, -⟩
  · rcases hf with rfl | rfl
    · exact (h93 he).elim
    · exact (h125 he).elim
  · exact hn
  · cases he

/-- A complete continuation at a comma selects the member after the consumed comma. -/
theorem comma_next (N : Nat) (f : UInt8) (frames bs t r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (hf : Br f) (hs : NearInterface.Json.skipWhitespace bs = 0x2C :: t)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) (.cont f) frames bs = some (r, ops)) :
    nextModel N f frames t = some (r, ops) := by
  rcases SerdeIgnContainer.phase_cases N false f 0x2C frames bs t r ops hf hs h with
    ⟨he, -⟩ | ⟨he, -⟩ | ⟨-, -, hn⟩
  · rcases hf with rfl | rfl <;> simp [SerdeIgnContainer.closing] at he
  · cases he
  · exact hn

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The actual full key/colon path retains the depth reserve and funds the next value entry. -/
theorem object_funded (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (maxP F N i : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hmodel : SerdeIgnMachineTrace.key SerdeIgnMachineTrace.keyBody (bs.drop i)
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (0x7B :: frames)) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 0x7B) [] memberCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(∃ j,
          ⌜i ≤ j + 1 ∧ j + 1 ≤ bs.length - r.length ∧
            SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (0x7B :: frames)
              (bs.drop (j + 1)) = some (r, ops)⌝ ∗
          credits Cg (cfg.regularOpCost + SerdeIgnBudget.regular cfg 64 (bs.length - r.length - (j + 1)) (frames.length + 1) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some 0x3A)) 0 l7 0x7B⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs (j + 1) ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr) } := by
  obtain ⟨q, e, j, key, rest, hq, he, hj, hquote, hcolon, hkey, hqe, hnext⟩ :=
    key_indices bs i _ _ hi hmodel
  have hj_lt := SerdeNextKey.getElem_lt hcolon
  have hdepth : frames.length + 1 ≤ bs.length - r.length - (j + 1) := by
    simpa only [SerdeIgnBudget.active, List.length_cons] using
      SerdeIgnBudget.active_le_remaining N .val (0x7B :: frames) bs r ops (j + 1) hnext
  have hjQ : j + 1 ≤ bs.length - r.length := by omega
  have hQi : i ≤ j + 1 := by omega
  have hsplit : bs.length - r.length - i = (j + 1 - i) + (bs.length - r.length - (j + 1)) := by omega
  have hkcost := cost_le_entry cfg i q e j (by omega) hqe (by omega)
  have hcost : SerdeIgnMember.cost cfg i q e j +
      (cfg.regularOpCost + SerdeIgnBudget.regular cfg 64 (bs.length - r.length - (j + 1)) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ≤
      SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R := by
    rw [hsplit, regular_split cfg _ _ _ hdepth, regular_entry cfg _ _ hdepth]
    omega
  iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H128 Hrd He Hhex HF]
  · iapply object_next cfg lim d inst mi A n g ta hm hd Cg
      (cfg.regularOpCost + SerdeIgnBudget.regular cfg 64 (bs.length - r.length - (j + 1)) (frames.length + 1) +
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

set_option maxRecDepth 100000 in
/-- Either actual member path retains its reserve, pays the loop branch, and funds the next value entry. -/
theorem next_funded (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr cap l3 l4 l6 l7 : UInt32) (l5 : UInt64)
    (f : UInt8) (maxP F N i : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hf : Br f) (hmodel : nextModel N f frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) +
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
          credits Cg (cfg.regularOpCost + SerdeIgnBudget.regular cfg 64 (bs.length - r.length - j) (frames.length + 1) +
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
    have hiQ : i ≤ bs.length - r.length := by omega
    have hdepth : frames.length + 1 ≤ bs.length - r.length - i := by
      simpa only [SerdeIgnBudget.active, List.length_cons] using
        SerdeIgnBudget.active_le_remaining N .val (0x5B :: frames) bs r ops i hmodel
    have hentry := regular_entry cfg (bs.length - r.length - i) (frames.length + 1) hdepth
    iintro ⟨#HC, Hc, Hg, H128, Hrd, He, Hhex, HF⟩
    iapply mwpi_wand
    isplitl [Hc Hg H128 Hrd He Hhex HF]
    · iapply array_next cfg lim d inst mi Cg
        (cfg.regularOpCost + SerdeIgnBudget.regular cfg 64 (bs.length - r.length - i) (frames.length + 1) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
        de s l3 l4 l6 l7 l5 iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr)
      iframe Hg H128 Hrd He Hhex HF
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      simp only [SerdeIgnBudget.memberAllowance, ite_true, Nat.add_mul]
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
    · iapply object_funded cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr cap l3 l4 l6 l7 l5
        maxP F N i frames bs r ops Fr hs hde hlen hptr hi hmodel
      iframe HC Hg H128 Hrd He Hhex HF
      simp only [SerdeIgnBudget.memberAllowance, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false, Nat.zero_mul, Nat.zero_add]
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

set_option maxRecDepth 100000 in
/-- The complete actual first-member iteration retains the member reserve and its control allowance. -/
theorem first_funded (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l4 l6 l7 : UInt32) (l5 : UInt64) (f : UInt8) (c : UInt8) (cap : UInt32)
    (maxP F N i q : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hf : Br f) (h93 : c ≠ 0x5D) (h125 : c ≠ 0x7D) (h44 : c ≠ 0x2C) (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some c)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) (.opened f) frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnBudget.regular cfg (SerdeIgnBudget.openedAllowance f) (bs.length - r.length - i) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 0 l4 l5 l6 l7 f.toUInt32) [] SerdeIgnClosing.iterationCode
      { normal := fun vs fr => iprop(⌜nextModel N f frames (bs.drop (q)) = some (r, ops)⌝ ∗
          credits Cg (13 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
            SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q)) (frames.length + 1) +
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
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + (bs.length - r.length - (q)) := by omega
  have hcharge := SerdeIgnBudget.first_cost cfg f (wsLen (bs.drop i))
    (bs.length - r.length - (q)) (frames.length + 1) hdepth
  have hcost : (162 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
      (13 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q)) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ≤
      SerdeIgnBudget.regular cfg (SerdeIgnBudget.openedAllowance f) (bs.length - r.length - i) (frames.length + 1) +
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
        SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q)) (frames.length + 1) +
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

set_option maxRecDepth 100000 in
/-- The complete actual comma iteration retains the member reserve and its control allowance. -/
theorem comma_funded (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l4 l6 l7 : UInt32) (l5 : UInt64) (f : UInt8) (cap : UInt32)
    (maxP F N i q : Nat) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (Fr : IProp GF)
    (hf : Br f) (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some 0x2C)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) (.cont f) frames (bs.drop i) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 1 l4 l5 l6 l7 f.toUInt32) [] SerdeIgnClosing.iterationCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(⌜nextModel N f frames (bs.drop (q + 1)) = some (r, ops)⌝ ∗
          credits Cg (9 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
            SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜k = 1 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 l4 (optByte (some 0x2C)) 0x2C l7 f.toUInt32⌝ ∗
          rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hq_lt hb
  have hs : NearInterface.Json.skipWhitespace (bs.drop i) = 0x2C :: bs.drop (q + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop, ← hq, hdr]
  have hnext := comma_next N f frames (bs.drop i) _ r ops hf hs hmodel
  have hdepth := next_depth N f frames bs r ops (q + 1) hf (by omega) hnext
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + 1 + (bs.length - r.length - (q + 1)) := by omega
  have hcharge := SerdeIgnBudget.comma_cost cfg f (wsLen (bs.drop i))
    (bs.length - r.length - (q + 1)) (frames.length + 1) hdepth
  have hcost : (191 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
      (9 * cfg.regularOpCost + SerdeIgnBudget.memberAllowance f * cfg.regularOpCost +
        SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ≤
      SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) +
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
        SerdeIgnBudget.regular cfg 0 (bs.length - r.length - (q + 1)) (frames.length + 1) +
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

end Proof
end WNear.Binary.SerdeIgnMemberBudget
