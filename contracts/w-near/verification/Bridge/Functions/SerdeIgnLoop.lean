import Bridge.Functions.SerdeIgnMemberBudget

/-! The complete actual container loop and member suffix of function 81.
The single-credit invariant retains the exact pop prefix, continuation trace,
frame contents, cursor and scratch allocation. The rejecting bytecode remains
present and is bypassed only by checked successful branches.

This does not yet assemble the value loop, prologue and final cleanup into a
full f81 contract or discharge IgnoreHyp, growth room or whole-object gas. -/

namespace WNear.Binary.SerdeIgnLoop
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
      SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) +
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
    credits Cg (SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
        (bs.length - r.length - i) (frames.length + 1) +
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
    have hreg : SerdeIgnBudget.regular cfg 0 (bs.length - r.length - i) (frames.length + 1) ≤
        SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) := by
      unfold SerdeIgnBudget.regular
      apply Nat.mul_le_mul_right
      omega
    cases frames with
    | nil =>
      iapply mwpi_wand
      isplitl [Hc HR]
      · iapply SerdeIgnClosing.funded_empty cfg lim d inst mi A n g ta hm hd Cg R
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
      · iapply SerdeIgnClosing.funded_nonempty cfg lim d inst mi A n g ta hm hd Cg R
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
          mpay
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
    · iapply SerdeIgnMemberBudget.first_funded cfg lim d inst mi A n g ta hm hd Cg R
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
      mpay
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
    · iapply SerdeIgnMemberBudget.comma_funded cfg lim d inst mi A n g ta hm hd Cg R
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
        (SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      resources n s de ptr p cap maxP hl F live bs i frames Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 current.toUInt32) [] loopCode
      (post cfg inst mi n Cg R s de ptr p cap maxP hl F live frames bs r ops Fr) := by
  iintro ⟨#HC, Hc, HR⟩
  unfold loopCode
  iapply MemCpy.mwpi_loop0 (Cg := Cg)
    (R := SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
      (bs.length - r.length - i) (frames.length + 1) + SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)
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
        (SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) +
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
          SerdeIgnBudget.regular cfg 0 (bs.length - r.length - j) (fs.length + 1) +
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
      mpay
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
      mpay
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
      SerdeIgnBudget.regular cfg 64 (bs.length - r.length - i) (frames.length + 1) +
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
        (SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) +
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
    · iapply SerdeIgnMemberBudget.next_funded cfg lim d inst mi A n g ta hm hd Cg (3 * cfg.regularOpCost + R)
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
        (SerdeIgnBudget.regular cfg (if opened then SerdeIgnBudget.openedAllowance current else 0)
          (bs.length - r.length - i) (frames.length + 1) +
          SerdeIgnTrace.extraCost cfg F cap frames.length ops + R)) ∗
      resources n s de ptr p cap maxP hl F live bs i frames (caller n g gt s Fr) ⊢
    mwpi cfg lim d (fr81 inst mi de s (if opened then 0 else 1) l4 l5 l6 l7 current.toUInt32) [] ((SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).drop 3)
      (suffixPost cfg inst mi n g Cg R gt s de ptr p cap maxP hl F live frames bs r ops Fr) := by
  rw [suffixCode_at]
  exact suffix cfg lim d inst mi A n g ta hm hd Cg R gt s de ptr p cap maxP hl F live frames bs r ops Fr
    i N opened current l4 l6 l7 l5 hs hstack hde hlen hptr hcurrent hframes hi hmodel

end Proof
end WNear.Binary.SerdeIgnLoop
