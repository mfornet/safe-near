import Bridge.Functions.SerdeStructObjModelState
import Bridge.Functions.SerdeStructObjKeyState
import Bridge.Functions.SerdeColonSuccess
import Bridge.Functions.SerdeValueState
import Bridge.Functions.SerdeIgnLoop


namespace WNear.Binary.SerdeIgnValueEntry
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)

/-- Cursor/continuation facts after a scalar behind the real whitespace prefix. -/
theorem scalar_indices (N : Nat) (f : UInt8) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (i q : Nat) (b : UInt8) (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some b)
    (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val (f :: frames)
      (bs.drop i) = some (r, ops)) :
    ∃ rest e, vSkip (bs.drop q) = some rest ∧ e = bs.length - rest.length ∧ q < e ∧
      e ≤ bs.length - r.length ∧
      SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont f) frames (bs.drop e) = some (r, ops) := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hq_lt hb
  have hskip : NearInterface.Json.skipWhitespace (bs.drop i) = b :: bs.drop (q + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop, ← hq, hdr]
  obtain ⟨rest, hv, hp⟩ := SerdeIgnScalar.scalar_step N (f :: frames) (bs.drop i) r ops b _ hskip hb5B hb7B hmodel
  rw [← hdr] at hv
  simp only [SerdeIgnMachineTrace.pop, Bool.false_eq_true, ite_false] at hp
  have hsuf := IgnoreShallow.vSkip_suf hv
  have hdrop := JsonSuffix.drop_suf' hsuf
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  have hg := SerdeIgnMachineTrace.run_good vSkip SerdeIgnMachineTrace.keyBody
    (fun _ _ => vSkip_length) SerdeIgnMachineTrace.keyBody_length N (.cont f) frames rest
  have hrest := (hg r ops hp).2.1
  refine ⟨rest, bs.length - rest.length, hv, rfl, by omega, by omega, ?_⟩
  rw [hdrop]
  exact hp

/-- The scalar value-entry prefix leaves the complete outer-frame reserve untouched. -/
theorem scalar_budget (cfg : WasmConfig) (w consumed remaining depth : Nat)
    (hc : 0 < consumed) (hd : depth ≤ remaining) :
    (125 + 96 * w) * cfg.regularOpCost + 7 * cfg.regularOpCost +
      (470 * consumed - 73) * cfg.regularOpCost +
      (5 * cfg.regularOpCost + SerdeIgnBudget.regular cfg 0 remaining depth) ≤
      SerdeIgnBudget.regular cfg 64 (w + consumed + remaining) depth := by
  have hh : (125 + 96 * w) + 7 + (470 * consumed - 73) +
      (5 + (0 + 470 * remaining - 110 * depth)) ≤
      64 + 470 * (w + consumed + remaining) - 110 * depth := by omega
  simpa only [SerdeIgnBudget.regular, Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost hh

/-- A top-level scalar finishes without any vector operation. -/
theorem top_indices (N : Nat) (bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (i q : Nat) (b : UInt8) (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some b)
    (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val []
      (bs.drop i) = some (r, ops)) :
    vSkip (bs.drop q) = some r ∧ q < bs.length - r.length ∧ ops = [] := by
  have hq_lt := SerdeNextKey.getElem_lt hb
  have hdr := SerdeIgnInt.drop_cons hq_lt hb
  have hskip : NearInterface.Json.skipWhitespace (bs.drop i) = b :: bs.drop (q + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_drop, ← hq, hdr]
  obtain ⟨rest, hv, hp⟩ := SerdeIgnScalar.scalar_step N [] (bs.drop i) r ops b _ hskip hb5B hb7B hmodel
  rw [← hdr] at hv
  simp only [SerdeIgnMachineTrace.pop, Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨hr, hops⟩ := hp
  rw [hr] at hv
  have hstrict := IgnoreShallow.vSkip_strict hv
  simp only [List.length_drop] at hstrict
  exact ⟨hv, by omega, hops.symm⟩

/-- The top scalar prefix leaves eight operations for the actual success cleanup. -/
theorem top_budget (cfg : WasmConfig) (w consumed : Nat) (hc : 0 < consumed) :
    (125 + 96 * w) * cfg.regularOpCost + 7 * cfg.regularOpCost +
      (470 * consumed - 31) * cfg.regularOpCost + 8 * cfg.regularOpCost ≤
      (109 + 470 * (w + consumed)) * cfg.regularOpCost := by
  have h : (125 + 96 * w) + 7 + (470 * consumed - 31) + 8 ≤ 109 + 470 * (w + consumed) := by omega
  simpa only [Nat.add_mul] using Nat.mul_le_mul_right cfg.regularOpCost h

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pending_entry (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
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
      credits Cg (SerdeIgnBudget.regular cfg 64 (bs.length - r.length - i) (frames.length + 1) +
        SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 1 0 l5 l6 l7 f.toUInt32) [] SerdeIgnOpening.entryCode
      { normal := fun vs fr => iprop(∃ e,
          ⌜q < e ∧ e ≤ bs.length - r.length ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.cont f) frames (bs.drop e) = some (r, ops)⌝ ∗
          credits Cg (5 * cfg.regularOpCost + SerdeIgnBudget.regular cfg 0 (bs.length - r.length - e) (frames.length + 1) +
            SerdeIgnTrace.extraCost cfg F cap frames.length ops + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 1 0 (optByte (some b)) 0 b.toUInt32 f.toUInt32⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs e ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  obtain ⟨rest, e, hv, he, hqe, heQ, hsub⟩ := scalar_indices N f frames bs r ops i q b hq hb hb5B hb7B hmodel
  have hdepth : frames.length + 1 ≤ bs.length - r.length - e := by
    simpa only [SerdeIgnBudget.active] using SerdeIgnBudget.active_le_remaining N (.cont f) frames bs r ops e hsub
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + (e - q) + (bs.length - r.length - e) := by omega
  have hcharge := scalar_budget cfg (wsLen (bs.drop i)) (e - q) (bs.length - r.length - e) (frames.length + 1) (by omega) hdepth
  rw [← hsplit] at hcharge
  let K := 5 * cfg.regularOpCost + SerdeIgnBudget.regular cfg 0 (bs.length - r.length - e) (frames.length + 1) +
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

set_option maxRecDepth 100000 in
/-- The actual whitespace/presence prefix establishes the successful dispatch cursor. -/
theorem peek_entry (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64)
    (bs : List UInt8) (i q : Nat) (b : UInt8) (Fr : IProp GF)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some b) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗
      credits Cg ((132 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 l8) []
      (SerdeIgnContainer.peekCode 4 ++ SerdeIgnScalar.presentCode)
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some b)) l6 l7 l8⌝ ∗ rd n de ptr bs q ∗ Fr) } := by
  iintro ⟨#HC, Hc, Hrd, HF⟩
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc Hrd HF]
  · iapply SerdeIgnContainer.peek_success cfg lim d inst mi A n g ta hm hd Cg (7 * cfg.regularOpCost + R)
      4 de s ptr l3 l4 l6 l7 l8 l5 bs i Fr hi hlen hptr hde
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
    iapply SerdeIgnScalar.present cfg lim d inst mi Cg R de s l3 l4 l6 l7 l8 b (iprop(rd n de ptr bs q ∗ Fr))
    iframe Hc Hrd HF
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

set_option maxRecDepth 100000 in
/-- The complete top scalar entry follows the actual success exit with its empty physical trace. -/
theorem top_entry (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (de s ptr p cap l3 l6 l7 l8 : UInt32) (l5 : UInt64)
    (bs r : List UInt8) (ops : List SerdeIgnTrace.Op) (i q maxP hl F N : Nat) (live : List (Nat × Nat)) (b : UInt8) (Fr : IProp GF)
    (hs : 128 ≤ s.toNat) (hs32 : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hq : q = i + wsLen (bs.drop i)) (hb : bs[q]? = some b) (hws : NearInterface.Json.isWhitespace b = false)
    (hb5B : b ≠ 0x5B) (hb7B : b ≠ 0x7B)
    (hmodel : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1) .val []
      (bs.drop i) = some (r, ops)) :
    SerdeIgnMember.code (GF := GF) n maxP inst mi A ∗
      credits Cg ((109 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs i ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 1 l5 l6 l7 l8) [] SerdeIgnOpening.entryCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(⌜ops = [] ∧ k = 2⌝ ∗ credits Cg (8 * cfg.regularOpCost + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 1 1 (optByte (some b)) 0 b.toUInt32 l8⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ rd n de ptr bs (bs.length - r.length) ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
  obtain ⟨hv, hqe, hops⟩ := top_indices N bs r ops i q b hq hb hb5B hb7B hmodel
  have hsplit : bs.length - r.length - i = wsLen (bs.drop i) + (bs.length - r.length - q) := by omega
  have hcharge := top_budget cfg (wsLen (bs.drop i)) (bs.length - r.length - q) (by omega)
  rw [← hsplit] at hcharge
  iintro ⟨#HC, Hc, H32, Hst, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
  iunfold SerdeIgnMember.code at HC
  icases HC with ⟨#CS, #CE, #F652⟩
  iunfold SerdeIgnSegments.code at CS
  icases CS with ⟨#C81, -⟩
  unfold SerdeIgnOpening.entryCode
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hg H128 Hrd He Hhex Hid HF]
  · iapply peek_entry cfg lim d inst mi A n g ta hm (by omega) Cg
      ((470 * (bs.length - r.length - q) - 31) * cfg.regularOpCost + (8 * cfg.regularOpCost + R))
      de s ptr l3 1 l6 l7 l8 l5 bs i q b
      (iprop(stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
        g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      (by omega) (by omega) hptr hi hq hb
    iframe C81 Hrd H32 Hst Hg H128 He Hhex Hid HF
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul] at hcharge ⊢
    omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr ⟨Hc, %⟨hvs, hfr⟩, Hrd, H32, Hst, Hg, H128, He, Hhex, Hid, HF⟩
    subst hvs; subst hfr
    simp only [Post.mseq_normal]
    iapply mwpi_wand
    isplitl [Hc Hrd H32 Hst Hg H128 He Hhex Hid HF]
    · iapply SerdeIgnScalar.top_block cfg lim d inst mi A n g ta hm hd Cg (8 * cfg.regularOpCost + R)
        gt de s ptr p cap l3 l6 l7 l8 bs r q (bs.length - r.length) maxP hl F live b Fr
        hs hde hs32 hlen hptr hb rfl hws hb5B hb7B hv
      iframe C81 CE F652 Hc H32 Hst Hg H128 Hrd He Hhex Hid HF
    iunfold Post.wand
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    isplit
    · iintro %k %vs %fr ⟨Hc, %⟨hk, hvs, hfr⟩, H32, Hst, Hg, H128, Hrd, He, Hhex, Hid, HF⟩
      isplitr
      · ipureintro; exact ⟨hops, hk⟩
      iframe Hc H32 Hst Hg H128 Hrd He Hhex Hid HF
      ipureintro; exact ⟨hvs, hfr⟩
    isplit
    · iintro %vs %fr H; iexfalso; iexact H
    · iintro H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  · iintro H; iexfalso; iexact H

end Proof

end WNear.Binary.SerdeIgnValueEntry


namespace WNear.Binary.SerdeIgnValueEntry
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnMachineStack

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
/-- Adapt the actual opening entry to the shared 128-byte value-loop stack, retaining its lower frame. -/
theorem opening_entry128 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
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
      credits Cg (SerdeIgnBudget.regular cfg (if frames.length = 0 then 109 else 64)
          (bs.length - r.length - i) frames.length + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (flag frames) l4 l5 l6 l7 (current fallback frames)) [] SerdeIgnOpening.entryCode
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = saveOps frames ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.opened opened) frames (bs.drop (q + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' +
            (6 * cfg.regularOpCost + SerdeIgnBudget.regular cfg (SerdeIgnBudget.openedAllowance opened)
              (bs.length - r.length - (q + 1)) (frames.length + 1) + R)) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some opened)) opened.toUInt32 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 128) 128 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (q + 1) ∗ Fr) } := by
  have hfixed : (if frames.length = 0 then 109 else 60) ≤ (if frames.length = 0 then 109 else 64) := by split <;> omega
  have hreg : SerdeIgnBudget.regular cfg (if frames.length = 0 then 109 else 60)
      (bs.length - r.length - i) frames.length ≤
      SerdeIgnBudget.regular cfg (if frames.length = 0 then 109 else 64) (bs.length - r.length - i) frames.length := by
    unfold SerdeIgnBudget.regular
    apply Nat.mul_le_mul_right
    omega
  iintro ⟨#HC, Hc, Hg, H128, Hvt, Hst, Hrd, HF⟩
  iunfold SerdeIgnMember.code at HC
  icases HC with ⟨#CS, -⟩
  icases VecFromElem.stk_split n (s.toNat - 128) 48 80 $$ H128 with ⟨H48, H80⟩
  rw [show s.toNat - 128 + 48 = s.toNat - 80 by omega]
  iapply mwpi_wand
  isplitl [Hc Hg H48 H80 Hvt Hst Hrd HF]
  · iapply SerdeIgnOpening.entry_funded cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap idx fallback l4 l6 l7 l5
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

end Proof
end WNear.Binary.SerdeIgnValueEntry
