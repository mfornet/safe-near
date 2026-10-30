import Bridge.Functions.DepositBodyNew

/-!
# `near_deposit` (232): the zero deposit, and the function's specification (M8)

* `body232_pos`: no deposit: `begin_panic("Requires positive attached deposit")` (664, `PanicSpecD`),
  the host unchanged by `attached_deposit`.
* `f232_spec`: 232 as an `MFunSpecT`, on every outcome (`case232`): it returns on `ok` (`Q232`, the
  host as `Post232`), it traps with the outcome's text otherwise (`T232`); the cost `cost232`.
-/

namespace WNear.Binary.DepositBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod iface ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA join64' split64' stkW stkB)
open WNear.Binary.BorshInt (stk_bytes')
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn)
open WNear.Binary.DepositTail (logText)
open WNear.Binary.PanicStr (panicCode panicSlot panicked)
open WNear.Binary.DepositPanicSpec (MFunSpecT_persistent hookRes pPre PanicSpecD)
open WNear.Binary.DepositSeg (LenUp)
open WNear.Binary.DepositSegAll (codeSeg)
open WNear.Binary.InternalDepositOverflow (textSupply)
open WNear.Binary.NewBody (keep)
open WNear.Binary.EnvGetters (dslot dCode depLo depHi)

/-- The cost of 232 with no deposit. -/
def costPos (cfg : WasmConfig) (F : Nat) (h : NearState) (K664 : Nat → NewBody.Keep → Nat) : Nat :=
  500 * cfg.regularOpCost + attachedDepositUse h + K664 F (keep h)

theorem dcase_zero (reg : Option Nat) (m T : Nat) : dcase 0 reg m T = .pos := by
  simp [dcase]

section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 64000000 in
/-- **232 with no deposit**: `begin_panic("Requires positive attached deposit")`. -/
theorem body232_pos (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (e inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (D : Nat)
    (hd : d + 27 + D < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s self : UInt32) (SP : Nat) (hSP : 400 ≤ SP)
    (hs : 144 + 80 + SP ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hal : s.toNat % 8 = 0)
    (pp pc pl : UInt32) (pre : List UInt8) (tb xb : List UInt8) (aidx : UInt32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (hroom : HeapRoomK 21 hl maxP)
    (h : NearState) (hview : h.context.isView = false) (hdep : depLo h ||| depHi h = 0)
    (hfitP : LogFits h NearDepositPanics.textPositive.length)
    (hovP : h.extCosts.cost "read_memory_byte" * NearDepositPanics.textPositive.length < 2 ^ 64)
    (reg : Option Nat) (m T : Nat)
    (C : IProp GF) [Persistent C] (lpc : UInt32) (Dp : IProp GF) (K664 : Nat → NewBody.Keep → Nat)
    (H664 : PanicSpecD cfg lim inst mi C n g ta A gt lpc maxP f664 SP Dp D 1050492 34 1050540 K664
      NearDepositPanics.textPositive)
    (Φ : Post NearState GF) :
    code232 e n maxP inst mi A mx ∗ C ∗ credits Cg (costPos cfg F h K664 + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - (224 + SP)) (224 + SP) ∗
      selfCells n self tb xb pp pc pl pre ∗
      stat232 n ta A lpc Dp aidx ∗ heapInv n maxP hl live F ∗ mhostPt h ∗
      (∀ hX, ⌜keep hX = keep h ∧ dcase (depOf h) reg m T ≠ .ok⌝ -∗
        panicked Cg hX (dcase (depOf h) reg m T).text -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 self, .i32 0, .i64 0, .i64 0, .i32 0, .i64 0, .i64 0], inst, mi⟩ [] f232.body Φ := by
  iintro ⟨#Hk, #HC, Hc, Hg, Stk, -, HT, Hinv, Hh, Wtr⟩
  iunfold code232 at Hk
  icases Hk with ⟨#Hseg, #HD, #F444, #F529, -, -, -, -, -, -, -, -, -, -, #F664⟩
  ihave #HIC : ifaceCode e inst mi A n mx $$ []
  · iunfold codeSeg, DepositTail.tailCode at Hseg
    icases Hseg with ⟨-, ⟨-, -, -, #H, -⟩, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold Interface.ifaceCode at HIC
    icases HIC with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  iunfold stat232 at HT
  icases HT with ⟨HI, H12, HDs, -, -, -, -, HPS, HH, HDp, -, -, HSt, -, Hvt⟩
  iunfold DepositTail.tailStat at HSt
  icases HSt with ⟨-, -, -, HLut, -, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have hd0 : depOf h = 0 := (EnvGetters.u64_or_eq_zero _ _).1 hdep
  have e0 : (s - 144).toNat = s.toNat - 144 := by rw [StorageBalanceBounds.tsub' _ _ (by simp; omega)]; simp
  have e24 : (s - 144 + 24).toNat = s.toNat - 120 := by simp [UInt32.toNat_add, e0]; omega
  have e32 : (s - 144 + 32).toNat = s.toNat - 112 := by simp [UInt32.toNat_add, e0]; omega
  icases stkSp (80 + SP) 144 (by omega) $$ Stk with ⟨Lo, Fr⟩
  icases stkSp 24 120 rfl $$ Fr with ⟨-, Fr⟩
  icases stkSp 8 112 rfl $$ Fr with ⟨O0, Fr⟩
  icases stkSp 8 104 rfl $$ Fr with ⟨O8, Fr⟩
  icases stkSp 8 96 rfl $$ Fr with ⟨U0, Fr⟩
  icases stkSp 8 88 rfl $$ Fr with ⟨U8, -⟩
  icases stk_bytes' $$ O0 with ⟨%ob0, %hob0, O0⟩
  icases stk_bytes' $$ O8 with ⟨%ob8, %hob8, O8⟩
  icases stk_bytes' $$ U0 with ⟨%ub0, %hub0, U0⟩
  icases stk_bytes' $$ U8 with ⟨%ub8, %hub8, U8⟩
  iunfold costPos at Hc
  generalize hKD : attachedDepositUse h = KD
  generalize hK664 : K664 F (keep h) = K6
  simp only [f232]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  have t0' : types[0]!.params.length = 1 := rfl
  have ha529 := hm.funcs 529 (by decide)
  icases stkSp (80 + SP - 32) 32 (by omega) $$ Lo with ⟨Lo, L32⟩
  mstep; mstep; mstep
  mcall (EnvGetters.f529_spec_host cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      (s - 144) (by omega) (by omega) (s - 144 + 24) ob0 ob8 hob0 hob8 h hview) using [Hg HI HDs L32 O0 O8 Hh]
      with (simp only [t0']; mstep_norm_full; omega)
  · iunfold EnvGetters.pre529
    ihave L32 := stkA (b := (s - 144).toNat - 32) (by omega) $$ L32
    ihave O0 := memBytes_addr (b := (s - 144 + 24).toNat) (by omega) $$ O0
    ihave O8 := memBytes_addr (b := (s - 144 + 24).toNat + 8) (by omega) $$ O8
    iframe Hg HI HDs L32 O0 O8 Hh
    ipureintro; rfl
  iunfold EnvGetters.post529 at HQ
  icases HQ with ⟨%hrs, Hg, HI, HDs, L32, O0, O8, Hh⟩
  subst hrs
  ihave O0 := memBytes_addr (b := (s - 144).toNat + 24) (by omega) $$ O0
  ihave O8 := memBytes_addr (b := (s - 144 + 32).toNat + 0) (by omega) $$ O8
  ihave U0 := memBytes_addr (b := (s - 144).toNat + 40) (by omega) $$ U0
  ihave U8 := memBytes_addr (b := (s - 144).toNat + 48) (by omega) $$ U8
  mstep; mstep; mstep; mstep; mstep [O8] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [U8] with simp
  mstep; mstep; mstep [O0] with simp
  simp only [U128From.decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [U0] with simp
  mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep_taken with (simp [Numeric.bool, Numeric.irelop64, hdep])
  mstep; mstep; mstep
  ihave Lo := stkJ2 (s.toNat - (224 + SP)) (by omega) (by omega) $$ Lo L32
  icases stkSp 80 SP (by omega) $$ Lo with ⟨-, Lo⟩
  have S664 := H664 (d + 1) Cg (s - 144) h hl live F aidx (by omega) (by omega) (by omega) (by omega)
    (DepositSeg.heapRoom_up hroom (DepositSeg.lenUp_refl hroom.1 hroom.2.1) (by omega)) hF hfitP hovP
  rw [hK664] at S664
  ihave #S664' := S664 $$ HC
  iapply mwpi_cons
  iapply (PanicStr.mwpi_callT' (i := 664) (a := A 664) (type := types[31]!) (inst := inst) (mi := mi)
    (code := f664) [.i32 1050492, .i32 34, .i32 1050540])
  isplitr
  · iexact S664'
  isplitr
  · iexact F664
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, hm.funcs 664 (by decide), rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Lo HH HI HPS Hinv Hvt HDp HLut Hh]
  · isplitr
    · ipureintro; rfl
    iunfold pPre
    iframe Hg HH HI HPS Hinv Hvt HDp HLut Hh
    iapply stkA2 (by omega) (by omega) $$ Lo
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HTr
    simp only [Post.mseq_trap, Post.mblock]
    iapply Wtr $$ %h %⟨rfl, by rw [hd0, dcase_zero]; exact fun h => DCase.noConfusion h⟩
    iapply panicked_conv ?_ $$ HTr
    rw [hd0, dcase_zero]; rfl

end Body

end WNear.Binary.DepositBody
