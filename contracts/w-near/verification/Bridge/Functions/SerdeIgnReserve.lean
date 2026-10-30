import Bridge.Functions.VecGrowZero

/-! # A common scratch-buffer contract for ignored-frame reserves -/

namespace WNear.Binary.SerdeIgnReserve

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ScratchGrow (sbuf fits capAfter fAfter hlAfter roomRes)

/-- The extra grow charge is paid only when the request does not fit. -/
def growthCost (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) : Nat :=
  if fits cap len k then 0 else 101 * cfg.regularOpCost + ScratchGrow.costRes cfg F cap len k

/-- Fitting reserves retain their tight allowance; growth keeps its allocation/copy charge explicit. -/
def cost (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) : Nat :=
  59 * cfg.regularOpCost + growthCost cfg F cap len k

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The actual callees of the fitting, allocating and reallocating reserve paths. -/
def code (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(VecGrowZero.code n maxP inst mi A ∗ VecGrow.waCode n maxP inst mi A)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code (GF := GF) n maxP inst mi A) := by
  unfold code; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Reserve through the real 698 chain, preserving the used prefix across every capacity case. -/
theorem f698_sbuf (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr cap k idx : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (bs : List UInt8) (hs : 80 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap : cap.toNat < 2 ^ 27)
    (hlen : bs.length + k.toNat < 2 ^ 27) (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) k) :
    code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f698 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗
        n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs))
      (fun _ => cost cfg F cap (UInt32.ofNat bs.length) k)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
        ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗
        n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
        n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗
        sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
          (capAfter cap (UInt32.ofNat bs.length) k) bs)) := by
  iintro #HC
  iunfold code at HC
  icases HC with ⟨#CZ, #CW⟩
  ihave #CW' := CW
  iunfold VecGrow.waCode at CW'
  icases CW' with ⟨#CGrow, #CApp⟩
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
  have hlt := s.toNat_lt
  iunfold MFunSpec
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, H80, Hvt, D0, D4, D8, Hsb⟩
  icases ScratchGrow.sbuf_pure $$ Hsb with ⟨%⟨hbl, hp0, hpc, hp1⟩, Hsb⟩
  by_cases hfit : fits cap (UInt32.ofNat bs.length) k
  · have hroom : (UInt32.ofNat bs.length).toNat + k.toNat ≤ cap.toNat := by
      simp only [fits, hL] at hfit; omega
    have key := VecAppend.f698_room (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt
      s vec (UInt32.ofNat bs.length) k cap (by omega) hvec hroom
    ihave #S := key $$ CApp
    clear key
    iunfold MFunSpec at S
    simp only [cost, growthCost, if_pos hfit, Nat.add_zero]
    icases stk_split n (s.toNat - 80) 64 16 $$ H80 with ⟨Lo, H16⟩
    ihave H16 := stk_addr (show s.toNat - 80 + 64 = s.toNat - 16 by omega) $$ H16
    iapply mwpInvoke_wand
    isplitl [Hg H16 D4 D8 Hc]
    · iapply S $$ %args %R [Hg H16 D4 D8] Hc
      try dsimp only
      iframe Hg H16 D4 D8
      ipureintro; exact ha
    isplit
    · iintro %rs ⟨Hc, %hrs, Hg, H16, D4, D8⟩
      try dsimp only
      iframe Hc
      isplitr
      · ipureintro; exact hrs
      iexists ptr, hl
      simp only [hlAfter, capAfter, fAfter, if_pos hfit]
      iframe Hg Hvt D0 D4 D8 Hsb
      iapply stk_join n (s.toNat - 80) 64 16
      rw [show s.toNat - 80 + 64 = s.toNat - 16 by omega]
      iframe Lo H16
    · iintro Htrap; iexact Htrap
  · have hgrow : cap.toNat < (UInt32.ofNat bs.length).toNat + k.toNat := by
      simp only [fits, hL] at hfit; omega
    have hroom := hr hfit
    have hgc := VecGrow.growCap_toNat cap (UInt32.ofNat bs.length + k) (by omega)
    have hsum : (UInt32.ofNat bs.length + k).toNat = bs.length + k.toNat := by
      rw [UInt32.toNat_add, hL]; omega
    have hcpos : 0 < (VecGrow.growCap cap (UInt32.ofNat bs.length + k)).toNat := by rw [hgc]; omega
    have hc0 : VecGrow.growCap cap (UInt32.ofNat bs.length + k) ≠ 0 := by
      intro h; rw [h] at hcpos; simp at hcpos
    have hused : bs.length ≤ (VecGrow.growCap cap (UInt32.ofNat bs.length + k)).toNat := by rw [hgc, hsum]; omega
    simp only [cost, growthCost, if_neg hfit]
    by_cases hzero : cap = 0
    · subst hzero
      have hnil : bs = [] := by simpa using hbl
      subst hnil
      have hptr : ptr = 1 := hp1 rfl
      subst hptr
      simp only [List.length_nil, show (UInt32.ofNat 0 : UInt32) = 0 from rfl, UInt32.zero_add] at *
      have hk0 : 0 < k.toNat := by simpa using hgrow
      have key := VecGrowZero.f698_alloc (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
        s vec k 1 idx maxP hl live F hs hvec hk0 (by omega) hroom
      ihave #S := key $$ CZ
      clear key
      iunfold MFunSpec at S
      iunfold sbuf at Hsb
      icases Hsb with ⟨_, _, _, Hheap⟩
      simp only [ite_true]
      have hcost : 480 * cfg.regularOpCost + SerdeString.costA cfg F (VecGrow.growCap 0 k) ≤
          59 * cfg.regularOpCost + (101 * cfg.regularOpCost + ScratchGrow.costRes cfg F 0 0 k) := by
        simp only [ScratchGrow.costRes, if_neg hfit, ScratchGrow.costGrow, ite_true, UInt32.zero_add]
        omega
      mcredits (480 * cfg.regularOpCost + SerdeString.costA cfg F (VecGrow.growCap 0 k) + R)
      iapply mwpInvoke_wand
      isplitl [Hg H80 Hvt Hheap D0 D4 D8 Hc]
      · iapply S $$ %args %R [Hg H80 Hvt Hheap D0 D4 D8] Hc
        try dsimp only
        iunfold VecGrowZero.pre
        iframe Hg H80 Hvt Hheap D0 D4 D8
        ipureintro; exact ha
      isplit
      · iintro %rs ⟨Hc, %hrs, HQ⟩
        try dsimp only
        iunfold VecGrowZero.post at HQ
        icases HQ with ⟨%p, Hg, H80, Hvt, D0, D4, D8, HA, Hb⟩
        iunfold SerdeString.heapS at HA
        rw [if_neg hc0]
        icases HA with ⟨%⟨hp0', hpc'⟩, %hl', %hhl, Hheap⟩
        iframe Hc
        isplitr
        · ipureintro; exact hrs
        iexists p, hl'
        simp only [hlAfter, capAfter, fAfter, if_neg hfit, UInt32.zero_add]
        iframe Hg H80 Hvt D0 D4 D8
        isplitr
        · ipureintro; exact hhl
        iunfold sbuf
        rw [if_neg hc0]
        isplitr
        · ipureintro; exact ⟨hused, hp0', hpc', by simp [hc0]⟩
        isplitl []
        · iapply VecFromElem.memBytes_nil
        iunfold block at Hb
        icases Hb with ⟨%junk, %hj, Hb⟩
        isplitl [Hb]
        · iexists junk
          iframe Hb
          ipureintro; simpa using hj
        iapply heapInv_mono n maxP hl' _ (max F 1) (F + 2) (by omega)
        iexact Hheap
      · iintro Htrap; iexact Htrap
    · have hpos : 0 < cap.toNat := by
        rcases Nat.eq_zero_or_pos cap.toNat with h | h
        · exact False.elim (hzero (UInt32.toNat_inj.mp (by simpa using h)))
        · exact h
      iunfold sbuf at Hsb
      icases Hsb with ⟨_, Hb, ⟨%junk, %hj, Hj⟩, Hheap⟩
      rw [if_neg hzero]
      ihave Hb := BorshFT.joinB bs junk rfl $$ [Hb Hj]
      · iframe Hb Hj
      have key := VecGrow.f698_grow (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
        s vec (UInt32.ofNat bs.length) k ptr cap idx maxP hl ((ptr.toNat, cap.toNat) :: live) F (bs ++ junk)
        hs hvec hp0 hpos hcap (by rw [hL]; exact hbl) hgrow (by rw [hL]; omega) (by simp; omega) (by simp) hroom
      ihave #S := key $$ CW
      clear key
      iunfold MFunSpec at S
      have hcost : 60 * cfg.regularOpCost + VecGrow.costGrow cfg F cap (VecGrow.growCap cap (UInt32.ofNat bs.length + k)) ≤
          59 * cfg.regularOpCost + (101 * cfg.regularOpCost + ScratchGrow.costRes cfg F cap (UInt32.ofNat bs.length) k) := by
        simp only [ScratchGrow.costRes, if_neg hfit, ScratchGrow.costGrow, if_neg hzero, VecGrow.costGrow]
        omega
      mcredits (60 * cfg.regularOpCost + VecGrow.costGrow cfg F cap (VecGrow.growCap cap (UInt32.ofNat bs.length + k)) + R)
      iapply mwpInvoke_wand
      isplitl [Hg H80 Hvt Hheap D0 D4 D8 Hb Hc]
      · iapply S $$ %args %R [Hg H80 Hvt Hheap D0 D4 D8 Hb] Hc
        try dsimp only
        iunfold VecGrow.pre712g
        iframe Hg H80 Hvt Hheap D0 D4 D8 Hb
        ipureintro; exact ha
      isplit
      · iintro %rs ⟨Hc, %hrs, HQ⟩
        try dsimp only
        iunfold VecGrow.post712g at HQ
        icases HQ with ⟨%p, Hg, H80, Hvt, D0, D4, D8, HA⟩
        iunfold VecGrow.reallocated at HA
        icases HA with ⟨%⟨hp0', hpc'⟩, ⟨%hl', %hhl, Hheap⟩, Hb, %junk2, %hj2, Hj2⟩
        iframe Hc
        isplitr
        · ipureintro; exact hrs
        iexists p, hl'
        simp only [hlAfter, capAfter, fAfter, if_neg hfit]
        iframe Hg H80 Hvt D0 D4 D8
        isplitr
        · ipureintro; exact hhl
        iunfold sbuf
        rw [if_neg hc0]
        isplitr
        · ipureintro; exact ⟨hused, hp0', hpc', by simp [hc0]⟩
        ihave Hb := BorshFT.splitB bs junk rfl $$ Hb
        icases Hb with ⟨Hb, Hj⟩
        iframe Hb
        isplitl [Hj Hj2]
        · iexists junk ++ junk2
          isplitr
          · ipureintro; simp; omega
          iapply BorshFT.joinB (a := p.toNat + bs.length) (b := p.toNat + cap.toNat) junk junk2 (by omega)
          iframe Hj Hj2
        ihave Hheap := heapInv_mono n maxP hl' _ (max F 1 + 1) (F + 2) (by omega) $$ Hheap
        simp only [List.erase_cons_head]
        iexact Hheap
      · iintro Htrap; iexact Htrap

end Proof
end WNear.Binary.SerdeIgnReserve
