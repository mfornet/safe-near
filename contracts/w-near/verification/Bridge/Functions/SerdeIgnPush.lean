import Bridge.Functions.SerdeIgnReserve

/-! # General scratch-frame pushes for ignored nested containers -/

namespace WNear.Binary.SerdeIgnPush

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ScratchGrow (sbuf fits capAfter fAfter hlAfter roomRes)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The optional-byte iterator first appends the byte, then exits. -/
def inv (n inst : Nat) (mi : ModuleInst) (Cg c R : Nat) (vec p b : UInt32) (len : Nat) (j : UInt8)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X fr =>
  iprop(∃ done : Bool,
    ⌜X = [] ∧ fr = ⟨#[.i32 vec, .i32 (UInt32.ofNat (if done then len + 1 else len)),
      .i32 (if done then 0 else b), .i32 (if done then 1 else 0), .i32 p], inst, mi⟩⌝ ∗
    credits Cg ((if done then 20 else 50) * c + R) ∗
    n ↦[wms][ p.toNat + len ] [if done then MemSet.byteOf b else j] ∗ P)

/-- A tight fixed instruction allowance, with reserve growth charged separately. -/
def cost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (len : Nat) : Nat :=
  140 * cfg.regularOpCost + SerdeIgnReserve.growthCost cfg F cap (UInt32.ofNat len) 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Push a present frame byte through the actual 84 on fitting, fresh and reallocating buffers. -/
theorem f84_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec b ptr cap idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (bs : List UInt8) (hs : 80 ≤ s.toNat) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length + 1 < 2 ^ 27)
    (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) 1) :
    SerdeIgnReserve.code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f84 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 1, .i32 b]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗
        n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs))
      (fun _ => cost cfg F cap bs.length)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
        ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) 1⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗
        n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) 1 ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + 1) ∗
        sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) 1) p
          (capAfter cap (UInt32.ofNat bs.length) 1) (bs ++ [MemSet.byteOf b]))) := by
  have key := SerdeIgnReserve.f698_sbuf (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega)
    Cg gt s vec ptr cap 1 idx maxP hl F live bs hs hvec hcap (by simpa using hlen) hr
  iintro #HC
  ihave #HC' := HC
  iunfold SerdeIgnReserve.code at HC'
  icases HC' with ⟨#CZ, -⟩
  iunfold VecGrowZero.code at CZ
  icases CZ with ⟨#C310, -, -, -, -, -, -, #F698⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at C310
    icases C310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha698 := hm.funcs 698 (by decide)
  have t14 : types[14]!.params.length = 2 := rfl
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, H80, Hvt, D0, D4, D8, Hsb⟩
  subst ha
  unfold f84
  simp only [cost, SerdeIgnReserve.cost] at key ⊢
  generalize hG : SerdeIgnReserve.growthCost cfg F cap (UInt32.ofNat bs.length) 1 = G at key ⊢
  repeat mstep
  mcall key using [Hg H80 Hvt D0 D4 D8 Hsb]
  · iframe Hg H80 Hvt D0 D4 D8 Hsb
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, H80, Hvt, D0, D4, D8, Hsb⟩
  subst hrs
  clear key hG
  icases ScratchGrow.sbuf_pure $$ Hsb with ⟨%⟨hused, hp0, hpc, -⟩, Hsb⟩
  have hroom : bs.length < (capAfter cap (UInt32.ofNat bs.length) 1).toNat := by
    by_cases h : fits cap (UInt32.ofNat bs.length) 1
    · simp only [capAfter, if_pos h]
      simp only [fits, hL, UInt32.toNat_one] at h
      omega
    · simp only [capAfter, if_neg h]
      rw [VecGrow.growCap_toNat _ _ (by omega)]
      have h1 : (UInt32.ofNat bs.length + 1).toNat = bs.length + 1 := by
        rw [UInt32.toNat_add, hL]; simp; omega
      rw [h1]; omega
  generalize hca : capAfter cap (UInt32.ofNat bs.length) 1 = ca at hroom hpc ⊢
  icases ScratchGrow.sbuf_push hroom $$ Hsb with ⟨%j, B, Hw⟩
  ispecialize Hw $$ %(MemSet.byteOf b)
  repeat mstep
  mstep [D8]
  repeat mstep
  mstep [D0]
  repeat mstep
  mcredits (cfg.regularOpCost + (50 * cfg.regularOpCost + R))
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 50 * cfg.regularOpCost + R)
    (I := inv n inst mi Cg cfg.regularOpCost R vec p b bs.length j
      iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗
        n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] ca ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗
        (n ↦[wms][ p.toNat + bs.length ] [MemSet.byteOf b] -∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) 1) p ca (bs ++ [MemSet.byteOf b])))) _ _ rfl
  isplitr
  · imodintro
    iintro %X %fr HI
    iunfold inv at HI
    icases HI with ⟨%done, %⟨hX, hfr⟩, Hc, B, HP⟩
    subst hX
    rw [hfr]
    icases HP with ⟨Hg, H80, Hvt, D0, D4, D8, Hw⟩
    cases done with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      repeat mstep
      mstep [B] with (simp [UInt32.toNat_add]; omega)
      rw [MemSet.storeBytes_i32_1]
      repeat mstep
      simp only [Post.mloop]
      mctrl_norm
      repeat mpay
      have hinc : UInt32.ofNat bs.length + 1 = UInt32.ofNat (bs.length + 1) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, hL]; simp <;> omega
      rw [hinc]
      iunfold inv
      iexists true
      simp only [ite_true]
      isplitr
      · ipureintro; trivial
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe B Hg H80 Hvt D0 D4 D8 Hw
    | true =>
      simp only [ite_true]
      repeat mstep
      simp only [Post.mloop]
      mctrl_norm
      repeat mpay
      repeat mstep
      mstep [D8]
      repeat mstep
      mcredits R
      ihave Hsb := Hw $$ B
      iframe Hc
      isplitr
      · ipureintro; simp [htype]
      iexists p, hl'
      iframe Hg H80 Hvt D0 D4 D8 Hsb
      ipureintro; exact hhl
  · iframe Hc
    inext
    iintro Hc
    iunfold inv
    iexists false
    simp only [Bool.false_eq_true, ite_false]
    iframe Hc B Hg H80 Hvt D0 D4 D8 Hw
    ipureintro; exact ⟨by trivial, rfl⟩

end Proof
end WNear.Binary.SerdeIgnPush
