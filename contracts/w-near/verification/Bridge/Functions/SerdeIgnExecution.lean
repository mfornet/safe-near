import Bridge.Functions.SerdeIgnValueEntry

namespace WNear.Binary.SerdeIgnExecution
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
    (hp : SerdeIgnLoop.Pops initial frames original ops) (hr : Room maxP hl cap initial.length original) :
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
    (hp : SerdeIgnLoop.Pops initial frames original ops) (hv : SerdeIgnTrace.Valid cap initial.length original) :
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
    (hp : SerdeIgnLoop.Pops initial frames original ops) :
    SerdeIgnTrace.endState cap initial.length original = SerdeIgnTrace.endState cap frames.length ops := by
  obtain ⟨popped, rfl, rfl⟩ := hp
  simpa only [List.length_append] using endState_prefix cap popped.length frames.length ops

theorem endFree_pops (F : Nat) (cap : UInt32) (initial frames : List UInt8) (original ops : List SerdeIgnTrace.Op)
    (hp : SerdeIgnLoop.Pops initial frames original ops) :
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

end WNear.Binary.SerdeIgnExecution

namespace WNear.Binary.SerdeIgnExecution
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
    (hp : SerdeIgnLoop.Pops initial frames original ops) (final : Nat) :
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

noncomputable def bodyCode : List Instr := SerdeIgnOpening.entryCode ++ SerdeIgnLoop.suffixCode

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
    credits Cg (SerdeIgnBudget.regular cfg (if frames.length = 0 then 109 else 64)
      (bs.length - r.length - i) frames.length + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
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
        (SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance f else 0)
          (bs.length - r.length - i) (frames.length + 1) + SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      fullResources n g ta A gt s de ptr idx maxP live bs i frames p cap F hl Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 f.toUInt32) [] SerdeIgnLoop.suffixCode
      (Post.mloop cfg Cg 0 []
        (valueInvariant cfg inst mi n g ta Cg R A gt s de ptr idx finalCap finalF maxP live bs r Fr H)
        (loopPost cfg inst mi n g ta Cg R A gt s de ptr idx finalCap finalF maxP live bs r Fr H)) := by
  iintro ⟨#HC, Hc, HR⟩
  iunfold fullResources at HR
  icases HR with ⟨Hg, H128, H32, Hvt, Hst, Hrd, He, Hhex, Hid, HF⟩
  iapply mwpi_wand
  isplitl [Hc Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF]
  · iapply SerdeIgnLoop.suffix cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap maxP hl F live frames bs r ops
      (iprop(AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr))
      i N opened f l4 l6 l7 l5 hs32 hs hde hlen hptr hf hframes hi hmodel
    iframe HC Hc
    iunfold SerdeIgnLoop.resources
    iunfold SerdeIgnLoop.caller
    iframe H32 Hst Hrd Hg H128 He Hhex Hvt Hid HF
  iunfold Post.wand
  simp only [SerdeIgnLoop.suffixPost]
  isplit
  · iintro %vs %fr H; iexfalso; iexact H
  isplit
  · iintro %k %vs %fr H
    icases H with (H | H)
    · icases H with ⟨%hk, H⟩
      subst hk
      iunfold SerdeIgnLoop.valueExit at H
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
        mpay
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
        iunfold SerdeIgnLoop.resources at HR
        icases HR with ⟨H32, Hst, Hrd, HX⟩
        iunfold SerdeIgnLoop.caller at HX
        icases HX with ⟨Hg, H128, He, Hhex, Hvt, Hid, HF⟩
        iunfold fullResources
        simp only [physical, List.tail_cons]
        iframe Hg H128 H32 Hvt Hst Hrd He Hhex Hid HF
    · icases H with ⟨%hk, H⟩
      subst hk
      iunfold SerdeIgnLoop.successExit at H
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
      iunfold SerdeIgnLoop.resources at HR
      icases HR with ⟨H32, Hst, Hrd, HX⟩
      iunfold SerdeIgnLoop.caller at HX
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
    · iapply SerdeIgnValueEntry.opening_entry128 cfg lim d inst mi A n g ta hm (by omega) Cg R
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
        simp only [SerdeIgnBudget.regular, SerdeIgnTrace.extraCost, physical, List.tail_nil,
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
      · iapply SerdeIgnValueEntry.pending_entry cfg lim d inst mi A n g ta hm hd Cg R gt de s ptr cap l6 l7 l5
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
      credits Cg ((110 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops + R) ∗
      fullResources n g ta A gt s de ptr idx maxP live bs i [] p cap F hl Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 0 1 0 0 0 0) [] [.loop .empty bodyCode]
      (loopPost cfg inst mi n g ta Cg R A gt s de ptr idx (SerdeIgnTrace.endState cap 0 ops).1
        (SerdeIgnTrace.endFreeBound F cap 0 ops) maxP live bs r Fr (HeapTrace hl cap 0 ops)) := by
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
    (R := SerdeIgnBudget.regular cfg 109 (bs.length - r.length - i) 0 + SerdeIgnTrace.extraCost cfg F cap 0 ops + R)
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
    simp only [SerdeIgnBudget.regular, Nat.mul_zero, Nat.sub_zero, Nat.add_mul]
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
      credits Cg ((113 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops + R) ∗
      fullResources n g ta A gt (sp - 32) de ptr idx maxP live bs i [] p cap F hl Fr ⊢
    mwpi cfg lim d (fr81 inst mi de (sp - 32) 0 1 0 0 0 0) [] mainCode
      { normal := fun vs _ => iprop(∃ p' hl', credits Cg R ∗ ⌜vs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
          rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr) } := by
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
    simp only [Nat.add_mul, Nat.sub_sub]
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
    mpay
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
      (fun _ => (166 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops)
      (fun _ rs => iprop(∃ p' hl', ⌜rs = [.i32 0] ∧ HeapTrace hl cap 0 ops hl'⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        SerdeIgnStack.state n maxP hl' live (SerdeIgnTrace.endFreeBound F cap 0 ops) (de + 12) p' (SerdeIgnTrace.endState cap 0 ops).1 [] ∗
        rd n de ptr bs (bs.length - r.length) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ Fr)) := by
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
      ((113 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops + R)
      gt sp de p cap sl maxP hl F live hsp hde
    iframe CS Hg H160 Hst
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    simp only [Nat.add_mul]
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
      (fun _ => (166 + 470 * (bs.length - r.length - i)) * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap 0 ops)
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
        ((166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
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

end Proof
end WNear.Binary.SerdeIgnExecution
