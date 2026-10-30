import Bridge.Functions.SerdeIgnFrame
import Bridge.Functions.VecGrowZero

/-! # Nonempty scratch frames for deeply nested ignored values -/

namespace WNear.Binary.SerdeIgnFrameStack

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.ScratchGrow (sbuf)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- Pop the most recently pushed byte, preserving the allocation, capacity and all earlier live blocks. -/
theorem f85_nonempty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec ptr cap : UInt32)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (b b0 b1 : UInt8)
    (hout : out.toNat + 2 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f85 Cg
      (fun args => iprop(⌜args = [.i32 out, .i32 vec]⌝ ∗ n ↦[i32][ vec.toNat ] ptr ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + 1) ∗
        n ↦[wms][ out.toNat ] [b0] ∗ n ↦[wms][ out.toNat + 1 ] [b1] ∗
        sbuf n maxP hl live F ptr cap (bs ++ [b])))
      (fun _ => 50 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ vec.toNat ] ptr ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ out.toNat ] [1] ∗ n ↦[wms][ out.toNat + 1 ] [b] ∗
        sbuf n maxP hl live F ptr cap bs)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, D0, D8, O0, O1, Hsb⟩
  subst ha
  iunfold sbuf at Hsb
  icases Hsb with ⟨%⟨hcap, hp0, hpc, hptr1⟩, Hb, ⟨%junk, %hjun, Hj⟩, Hinv⟩
  simp only [List.length_append, List.length_singleton] at hcap hjun
  have hlt := cap.toNat_lt
  have hne : UInt32.ofNat (bs.length + 1) ≠ 0 := by
    intro h
    have he := congrArg UInt32.toNat h
    simp only [UInt32.toNat_ofNat', UInt32.toNat_zero] at he
    omega
  ihave Hb := BorshFT.splitB bs [b] rfl $$ Hb
  icases Hb with ⟨Hb, Blast⟩
  simp only [f85]
  mstep; mstep; mstep
  mstep [D8]
  mstep
  mstep_taken with exact hne
  mstep; mstep; mstep; mstep
  have hpred : UInt32.ofNat (bs.length + 1) + 4294967295 = UInt32.ofNat bs.length := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.reduceToNat]
    omega
  rw [hpred]
  clear hpred
  repeat mstep
  mstep [D8]
  repeat mstep
  mstep [D0]
  repeat mstep
  mstep [Blast] with (simp [UInt32.toNat_add]; omega)
  simp only [SerdeKey.load8]
  repeat mstep
  mstep [O1]
  repeat mstep
  mstep [O0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  rw [show storeBytes (.i32 1) 1 = [1] by decide,
    show storeBytes (.i32 b.toUInt32) 1 = [b] by rw [MemSet.storeBytes_i32_1]; simp [MemSet.byteOf]]
  iframe D0 D8 O0 O1
  iunfold sbuf
  iframe Hb Hinv
  isplitr
  · ipureintro; exact ⟨by omega, hp0, hpc, hptr1⟩
  iexists b :: junk
  isplitr
  · ipureintro; simp; omega
  ihave Hj := AllocNewCell.memBytes_addr
    (show ptr.toNat + (bs ++ [b]).length = ptr.toNat + bs.length + [b].length by simp; omega) $$ Hj
  ihave Hj := BorshFT.joinB [b] junk rfl $$ [Blast Hj]
  · iframe Blast Hj
  simp only [List.singleton_append]
  iexact Hj

/-- Two iterations: first write the optional byte, then leave the iterator loop. -/
def pushInv (n inst : Nat) (mi : ModuleInst) (Cg c R : Nat) (vec p b : UInt32) (j : UInt8)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X fr =>
  iprop(∃ done : Bool,
    ⌜X = [] ∧ fr = ⟨#[.i32 vec, .i32 (if done then 1 else 0), .i32 (if done then 0 else b),
      .i32 (if done then 1 else 0), .i32 p], inst, mi⟩⌝ ∗
    credits Cg ((if done then 20 else 60) * c + R) ∗
    n ↦[wms][ p.toNat ] [if done then MemSet.byteOf b else j] ∗ P)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The first frame push allocates an eight-byte scratch buffer and installs the pushed byte. -/
theorem f84_initial (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec b idx : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (hs : 80 ≤ s.toNat) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hr : VecFromElem.roomFor hl maxP 8) :
    VecGrowZero.code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f84 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 1, .i32 b]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        VecFromElem.stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        AllocInv.heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] 1 ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗
        n ↦[i32][ vec.toNat + 8 ] 0))
      (fun _ => 600 * cfg.regularOpCost + SerdeString.costA cfg F 8)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
        ⌜hl' = hl ∨ hl' = VecFromElem.grownLen hl 8⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        VecFromElem.stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] 8 ∗ n ↦[i32][ vec.toNat + 8 ] 1 ∗
        sbuf n maxP hl' live (max F 1) p 8 [MemSet.byteOf b])) := by
  have hcap : VecGrow.growCap 0 1 = 8 := by decide +kernel
  have key := VecGrowZero.f698_alloc (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega)
    Cg gt s vec 1 1 idx maxP hl live F hs hvec (by decide) (by decide) (by rw [hcap]; exact hr)
  rw [hcap] at key
  iintro #HC
  ihave #HC' := HC
  iunfold VecGrowZero.code at HC'
  icases HC' with ⟨#C310, -, -, -, -, -, -, #F698⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at C310
    icases C310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha698 := hm.funcs 698 (by decide)
  have t14 : types[14]!.params.length = 2 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, H80, Hvt, Hheap, D0, D4, D8⟩
  subst ha
  unfold f84
  generalize hK : SerdeString.costA cfg F 8 = K at key ⊢
  repeat mstep
  mcall key using [Hg H80 Hvt Hheap D0 D4 D8]
  · iunfold VecGrowZero.pre
    iframe Hg H80 Hvt Hheap D0 D4 D8
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  clear key hK hcap
  iunfold VecGrowZero.post at HQ
  icases HQ with ⟨%p, Hg, H80, Hvt, D0, D4, D8, HA, Hblock⟩
  simp only [show VecGrow.growCap 0 1 = 8 from rfl]
  iunfold SerdeString.heapS at HA
  simp only [show (8 : UInt32) ≠ 0 by decide, ite_false]
  icases HA with ⟨%⟨hp0, hpc⟩, %hl', %hhl, Hheap⟩
  iunfold AllocInv.block at Hblock
  icases Hblock with ⟨%raw, %hraw, Hb⟩
  obtain ⟨j, junk, rfl⟩ : ∃ (j : UInt8) (junk : List UInt8), raw = j :: junk := by
    cases raw with
    | nil => simp at hraw
    | cons j junk => exact ⟨j, junk, rfl⟩
  ihave Hb := AllocNewCell.memBytes_eq (show j :: junk = [j] ++ junk from rfl) $$ Hb
  ihave Hb := BorshFT.splitB [j] junk rfl $$ Hb
  icases Hb with ⟨B, Junk⟩
  mcredits (90 * cfg.regularOpCost + R)
  repeat mstep
  mstep [D8]
  repeat mstep
  mstep [D0]
  repeat mstep
  mcredits (cfg.regularOpCost + (60 * cfg.regularOpCost + R))
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 60 * cfg.regularOpCost + R)
    (I := pushInv n inst mi Cg cfg.regularOpCost R vec p b j
      iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ VecFromElem.stk n (s.toNat - 80) 80 ∗
        AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
        n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] 8 ∗ n ↦[i32][ vec.toNat + 8 ] 0 ∗
        n ↦[wms][ p.toNat + 1 ] junk ∗
        AllocInv.heapInv n maxP hl' ((p.toNat, 8) :: live) (max F 1))) _ _ rfl
  isplitr
  · imodintro
    iintro %X %fr HI
    iunfold pushInv at HI
    icases HI with ⟨%done, %⟨hX, hfr⟩, Hc, B, HP⟩
    subst hX
    rw [hfr]
    icases HP with ⟨Hg, H80, Hvt, D0, D4, D8, Junk, Hheap⟩
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
      iunfold pushInv
      iexists true
      simp only [ite_true]
      isplitr
      · ipureintro; exact ⟨by trivial, rfl⟩
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe B Hg H80 Hvt D0 D4 D8 Junk Hheap
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
      iframe Hc
      isplitr
      · ipureintro; simp [htype]
      iexists p, hl'
      isplitr
      · ipureintro; exact hhl
      iframe Hg H80 Hvt D0 D4 D8
      iunfold sbuf
      simp only [List.length_singleton, show (8 : UInt32).toNat = 8 from rfl,
        show (8 : UInt32) ≠ 0 by decide, ite_false]
      iframe B Hheap
      isplitr
      · ipureintro; exact ⟨by decide, hp0, hpc, by simp⟩
      iexists junk
      iframe Junk
      ipureintro; simpa using hraw
  · iframe Hc
    inext
    iintro Hc
    iunfold pushInv
    iexists false
    simp only [Bool.false_eq_true, ite_false]
    iframe Hc B Hg H80 Hvt D0 D4 D8 Junk Hheap
    ipureintro; exact ⟨by trivial, rfl⟩

end Proof
end WNear.Binary.SerdeIgnFrameStack
