import Bridge.Functions.DepositF232

/-!
# `near_deposit` (232) as a function specification (M8)

`f232_spec`: from the token at `self` (`selfCells`), its statics (`stat232`), the heap, the frame
and the host `h`, with the account's record `reg` (`h.storage key`), 232 either returns, on the
outcome `ok` (`case232`), with the host as `Post232` and the new total supply at `self`, or traps,
on any other outcome, the host (up to gas, `keep`) panicked with the outcome's text.
-/

namespace WNear.Binary.DepositBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.DepositTail (logText)
open WNear.Binary.PanicStr (panicked)
open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent PanicSpecD)
open WNear.Binary.DepositSeg (LenUp)
open WNear.Binary.InternalDepositOverflow (textSupply)
open WNear.Binary.NewBody (keep)
open WNear.Binary.EnvGetters (depLo depHi)
open WNear.Binary.StorageBalanceBounds (u128Of)

/-- The balance of a registered account. -/
def regB (reg : Option (UInt64 × UInt64)) : Option Nat := reg.map fun p => p.1.toNat + 2 ^ 64 * p.2.toNat

/-- The outcome of 232. -/
def case232 (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) (T : Nat) : DCase :=
  dcase (depOf h) (regB reg) (minOf xb) T

/-- The amount deposited, as 232 computes it. -/
def amount232 (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) : Nat :=
  match reg with
  | some _ => depOf h
  | none => (aloOf h xb).toNat + 2 ^ 64 * (ahiOf h xb).toNat

/-- The amount's words, as the log formats them. -/
def amtLo (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) : UInt64 :=
  match reg with
  | some _ => depLo h
  | none => aloOf h xb
def amtHi (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) : UInt64 :=
  match reg with
  | some _ => depHi h
  | none => ahiOf h xb

/-- What 232 leaves of the host on `ok`. -/
def Post232 (e : Nat) (h : NearState) (key : List UInt8) (reg : Option (UInt64 × UInt64)) (xb : List UInt8)
    (st : Near.TrieOverlay.State) (bud : Nat) (h' : NearState) : Prop :=
  match reg with
  | some (x0, x1) => PostReg e h key (u128Of (x0.toNat + 2 ^ 64 * x1.toNat + depOf h)) st bud
      (logText (depLo h) (depHi h) h.context.predecessorAccountId) h'
  | none => PostNew e h key (u128Of (0 + 2 ^ 64 * 0 + ((aloOf h xb).toNat + 2 ^ 64 * (ahiOf h xb).toNat))) st bud
      (logText (aloOf h xb) (ahiOf h xb) h.context.predecessorAccountId) h'

/-- The cost of 232, activation excluded. -/
noncomputable def cost232 (cfg : WasmConfig) (F : Nat) (pl : UInt32) (h : NearState) (key : List UInt8)
    (reg : Option (UInt64 × UInt64)) (xb : List UInt8) (t0 t1 : UInt64)
    (K879 K664s K664p : Nat → NewBody.Keep → Nat) : Nat :=
  if depOf h = 0 then costPos cfg F h K664p
  else match reg with
    | some (x0, x1) => costReg cfg F pl h key x0 x1 t0 t1 h.context.predecessorAccountId K879
    | none => costUnreg cfg F pl h key xb t0 t1 h.context.predecessorAccountId K879 K664s

theorem dcase_some_m (dep B m T : Nat) : dcase dep (some B) m T = dcase dep (some B) 0 T := by
  unfold dcase amountOf
  simp only [reduceCtorEq, false_and, if_false]

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 232's precondition. -/
def pre232 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s self : UInt32) (SP : Nat) (t0 t1 : UInt64)
    (xb : List UInt8) (pp pc pl : UInt32) (pre : List UInt8) (lpc : UInt32) (Dp : IProp GF) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 self]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - (224 + SP)) (224 + SP) ∗
    selfCells n self (storeBytes (.i64 t0) 8 ++ storeBytes (.i64 t1) 8) xb pp pc pl pre ∗
    stat232 n ta A lpc Dp aidx ∗ heapInv n maxP hl live F ∗ mhostPt h)

/-- 232's return, on `ok`. -/
def Q232 (e n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s self : UInt32) (SP : Nat) (t0 t1 : UInt64)
    (xb : List UInt8) (pp pc pl : UInt32) (pre : List UInt8) (lpc : UInt32) (Dp : IProp GF) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (h : NearState) (key : List UInt8)
    (reg : Option (UInt64 × UInt64)) (st : Near.TrieOverlay.State) (bud : Nat) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = [] ∧ case232 h reg xb (t0.toNat + 2 ^ 64 * t1.toNat) = .ok⌝ ∗
    ∃ (hl' F' : Nat) (h' : NearState), ⌜F' ≤ F + 16 ∧ LenUp hl 16 hl' ∧ Post232 e h key reg xb st bud h'⌝ ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - (224 + SP)) (224 + SP) ∗
      selfCells n self (u128Of (t0.toNat + 2 ^ 64 * t1.toNat + amount232 h reg xb)) xb pp pc pl pre ∗
      stat232 n ta A lpc Dp aidx ∗ heapInv n maxP hl' live F' ∗ mhostPt h')

/-- 232's trap, on any other outcome. -/
def T232 (Cg : Nat) (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8) (T : Nat) : IProp GF :=
  iprop(⌜case232 h reg xb T ≠ .ok⌝ ∗ ∃ hX, ⌜keep hX = keep h⌝ ∗ panicked Cg hX (case232 h reg xb T).text)

theorem entryLocals_f232 (self : UInt32) :
    entryLocals f232 [.i32 self] = #[.i32 self, .i32 0, .i64 0, .i64 0, .i32 0, .i64 0, .i64 0] := rfl

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **`near_deposit`'s body (232)** as a function specification, on every outcome. -/
theorem f232_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType) (htype : type.results = [])
    (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (D : Nat)
    (hd : d + 27 + D < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s self : UInt32) (SP : Nat) (hSP : 400 ≤ SP)
    (hs : 144 + 80 + SP ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hal : s.toNat % 8 = 0)
    (hthis : self.toNat + 40 ≤ 2 ^ 32) (pp pc pl : UInt32) (pre : List UInt8)
    (hpre : pre.length = pl.toNat) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat) (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32)
    (t0 t1 : UInt64) (xb : List UInt8) (hxb : xb.length = 8) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (hroom : HeapRoomK 21 hl maxP)
    (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hview : h.context.isView = false) (hacc : h.storageAccounting = some st) (hcanon : Canon st)
    (hlink : StorageLink h st) (hproof : ProofBudget h st bud)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlimR : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true)
    (hutf : Utf8.utf8Ok h.context.predecessorAccountId = true)
    (hab : h.context.predecessorAccountId.length ≤ 64) (hab0 : 0 < h.context.predecessorAccountId.length)
    (hlim : withinLimit h.config.maxStorageKeyLen
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)).length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen 16 = true)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hbud : 4 * lookupProofBound (contractKey h.context.currentAccountId
      (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))) + 48 ≤ bud)
    (reg : Option (UInt64 × UInt64))
    (hstore : h.storage (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++
      h.context.predecessorAccountId)) = reg.map fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8)
    (hlog : ∀ lo hi : UInt64, LogStr.LogOk h (logText lo hi h.context.predecessorAccountId)
      (logText lo hi h.context.predecessorAccountId).length)
    (hfit16 : LogFits h 16) (hov16 : h.extCosts.cost "read_memory_byte" * 16 < 2 ^ 64)
    (hfitS : LogFits h textSupply.length) (hovS : h.extCosts.cost "read_memory_byte" * textSupply.length < 2 ^ 64)
    (hfitT : LogFits h NearDepositPanics.textTooSmall.length)
    (hovT : h.extCosts.cost "read_memory_byte" * NearDepositPanics.textTooSmall.length < 2 ^ 64)
    (hfitP : LogFits h NearDepositPanics.textPositive.length)
    (hovP : h.extCosts.cost "read_memory_byte" * NearDepositPanics.textPositive.length < 2 ^ 64)
    (C : IProp GF) [Persistent C] (lpc : UInt32) (Dp : IProp GF) (K879 K664s K664p : Nat → NewBody.Keep → Nat)
    (H879 : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f879 SP Dp D 1053016 21 1053040 K879 textSupply)
    (H664s : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f664 SP Dp D 1050556 21 1050580 K664s
      NearDepositPanics.textTooSmall)
    (H664p : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f664 SP Dp D 1050492 34 1050540 K664p
      NearDepositPanics.textPositive) :
    code232 e n maxP inst mi A mx ∗ C
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f232 Cg
        (pre232 n g ta A gt s self SP t0 t1 xb pp pc pl pre lpc Dp aidx maxP hl live F h)
        (fun _ => cost232 cfg F pl h
          (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))
          reg xb t0 t1 K879 K664s K664p)
        (Q232 e n g ta A gt s self SP t0 t1 xb pp pc pl pre lpc Dp aidx maxP hl live F h
          (pre ++ (bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId))
          reg st bud)
        (fun _ => T232 Cg h reg xb (t0.toNat + 2 ^ 64 * t1.toNat)) := by
  iintro ⟨#Hk, #HC⟩
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre232 at HP
  icases HP with ⟨%hargs, Hg, Stk, HS, HT, Hinv, Hh⟩
  subst hargs
  rw [entryLocals_f232]
  unfold cost232
  by_cases hd0 : depOf h = 0
  · rw [if_pos hd0]
    have hdep : depLo h ||| depHi h = 0 := (EnvGetters.u64_or_eq_zero _ _).2 hd0
    iapply body232_pos cfg lim d e inst mi A n g ta mx hm D hd Cg R gt s self SP hSP hs hs2 hal pp pc pl pre _ xb aidx
      maxP hl live F hF hroom h hview hdep hfitP hovP (regB reg) (minOf xb) (t0.toNat + 2 ^ 64 * t1.toNat) C lpc Dp K664p
      H664p _
    iframe Hk HC Hc Hg Stk HS HT Hinv Hh
    iintro %hX %⟨hk, hnok⟩ HTr
    simp only [Post.mfunc]
    iunfold T232
    isplitr
    · ipureintro; exact hnok
    iexists hX
    isplitr
    · ipureintro; exact hk
    iapply panicked_conv ?_ $$ HTr
    rfl
  rw [if_neg hd0]
  have hdep : depLo h ||| depHi h ≠ 0 := fun h0 => hd0 ((EnvGetters.u64_or_eq_zero _ _).1 h0)
  cases reg with
  | some p =>
    obtain ⟨x0, x1⟩ := p
    simp only
    iapply body232_reg cfg lim d e inst mi A n g ta mx hm D hd Cg R gt s self SP hSP hs hs2 hal hthis pp pc pl pre
      hpre hpl hl0 hpp t0 t1 x0 x1 xb aidx maxP hl live F hF (DepositSeg.heapRoom_up hroom (DepositSeg.lenUp_refl hroom.1 hroom.2.1) (by omega))
      h st hview hacc hcanon hlink hproof hvalid hlimR hutf hab hab0 hlim hvlim hreg hbud hstore hdep hlog hfit16 hov16
      hfitS hovS C lpc Dp K879 H879 _
    iframe Hk HC Hc Hg Stk HS HT Hinv Hh
    isplitl []
    · iintro %hl' %F' %h' %f' %⟨hF', hup, hpost, hok⟩ Hc Hg Lo HS HB Hinv Hh
      simp only [Post.mfunc]
      isplitr
      · ipureintro; simp [htype]
      iexists R
      iframe Hc
      iintro Hc
      iframe Hc
      iunfold Q232
      simp only [amount232]
      isplitr
      · ipureintro
        refine ⟨by simp, ?_⟩
        simp only [case232, regB, Option.map_some]
        rw [dcase_some_m]; exact hok
      iexists hl', F', h'
      iframe Hg Lo HS HB Hinv Hh
      ipureintro; exact ⟨by omega, hup.mono (by omega), hpost⟩
    · iintro %hX %⟨hk, hnok⟩ HTr
      simp only [Post.mfunc]
      iunfold T232
      isplitr
      · ipureintro; exact fun hc => hnok ((dcase_some_m _ _ _ _).symm.trans hc)
      iexists hX
      isplitr
      · ipureintro; exact hk
      iapply panicked_conv ?_ $$ HTr
      exact (congrArg DCase.text (dcase_some_m _ _ _ _)).symm
  | none =>
    simp only
    iapply body232_unreg cfg lim d e inst mi A n g ta mx hm D hd Cg R gt s self SP hSP hs hs2 hal hthis pp pc pl pre
      hpre hpl hl0 hpp t0 t1 xb hxb aidx maxP hl live F hF hroom
      h st hview hacc hcanon hlink hproof hvalid hlimR hutf hab hab0 hlim hvlim hreg hbud hstore hdep hlog hfit16 hov16
      hfitS hovS hfitT hovT C lpc Dp K879 K664s H879 H664s _
    iframe Hk HC Hc Hg Stk HS HT Hinv Hh
    isplitl []
    · iintro %hl' %F' %h' %f' %⟨hF', hup, hpost, hok⟩ Hc Hg Lo HS HB Hinv Hh
      simp only [Post.mfunc]
      isplitr
      · ipureintro; simp [htype]
      iexists R
      iframe Hc
      iintro Hc
      iframe Hc
      iunfold Q232
      simp only [amount232]
      isplitr
      · ipureintro; exact ⟨by simp, hok⟩
      iexists hl', F', h'
      iframe Hg Lo HS HB Hinv Hh
      ipureintro; exact ⟨hF', hup, hpost⟩
    · iintro %hX %⟨hk, hnok⟩ HTr
      simp only [Post.mfunc]
      iunfold T232
      isplitr
      · ipureintro; exact hnok
      iexists hX
      isplitr
      · ipureintro; exact hk
      iapply panicked_conv ?_ $$ HTr
      rfl

end Spec

end WNear.Binary.DepositBody
