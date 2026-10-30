import Bridge.Functions.ScratchGrow

/-! # The general Vec reserve chain's first allocation -/

namespace WNear.Binary.VecGrowZero

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr stk_open581 stk_close581 roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeString (heapS costA)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
/-- The general Vec allocator on positive byte capacity, retaining the allocation and every earlier live block. -/
theorem f713_alloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out size idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ob : List UInt8) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32) (hsp : 16 ≤ sp.toNat)
    (hsize : 0 < size.toNat) (hsize2 : size.toNat < 2 ^ 28) (hr : roomFor hl maxP size) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f713 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 size, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 40 * cfg.regularOpCost + costA cfg F size)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ vt n 1057464 idx ta (A 578) ∗ heapS n maxP hl live F size p ∗
          block n p.toNat size.toNat ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size)) := by
  iintro ⟨#Hcode, #H310⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha310 := hm.funcs 310 (by decide)
  have t13 : types[13]!.params.length = 2 := rfl
  have hs0 : size ≠ 0 := by intro h; subst h; simp at hsize
  obtain ⟨hlen0, hlen1, hroom, hmax⟩ := hr
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, Hs, Hvt, Hinv, Ho⟩
  subst ha
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  icases stk_open581 n sp hsp $$ Hs with ⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, O1, O2, O4, W8⟩
  unfold f713
  generalize hK : costA cfg F size = K
  simp only [costA] at hK
  have key := AllocWalk.f310_spec_walk (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega)
    Cg gt sp size 1 idx 0 maxP hl live F o1 o2 o4 hsp (by simp) (by simp) hsize hsize2 hlen0 hlen1 h1 h2 h4 hroom hmax
  rw [hK] at key
  clear hK hroom hmax hlen0 hlen1 h1 h2 h4
  mstep
  mstep
  iapply mwpi_cons
  iapply (NearLogic.mwpi_i32_eqz' (a := size) (rest := []))
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega, trivial⟩
  inext
  iintro Hc
  mctrl_norm
  have hz : Numeric.bool (size == 0) = 0 := by simp [Numeric.bool, hs0]
  rw [hz]
  mstep_not_taken with rfl
  repeat mstep
  mcall key using [Hg O1 O2 O4 Hvt Hinv]
  · iframe Hg O1 O2 O4 Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %hl', %hhl, Hinv, Hb⟩
  subst hrs
  clear key hz
  ihave Hinv := FmtSink.heapInv_bound (p := p.toNat) (s := size.toNat) (by simp) $$ Hinv
  icases Hinv with ⟨%hpb, Hinv⟩
  ihave HA : heapS n maxP hl live F size p $$ [Hinv]
  · iunfold heapS
    rw [if_neg hs0]
    isplitr
    · ipureintro; exact ⟨hp0, hpb⟩
    iexists hl'
    iframe Hinv
    ipureintro; exact hhl
  mcredits (10 * cfg.regularOpCost + R)
  repeat mstep
  mstep [Ho4]
  repeat mstep
  mstep [Ho0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Ho0 Ho4 HA Hb
  iapply stk_close581 n sp hsp
  iframe HO W8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`finish_grow(out, c, 1, cur, _)`** (714) with no current memory (`cur.ptr = 0`):
the Vec allocation helper (713), `Ok((p, c))` at `out`. -/
theorem f714_alloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c cur x : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (ob : List UInt8) (hs : 32 ≤ s.toNat) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hc0 : 0 < c.toNat) (hc : c.toNat < 2 ^ 28) (hr : roomFor hl maxP c) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 713 ↪[wf] FuncInst.wasm types[31]! inst f713
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f714 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 c, .i32 1, .i32 cur, .i32 x]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 32) 32 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗
          n ↦[i32][ cur.toNat ] 0 ∗ n ↦[wms][ out.toNat ] ob))
        (fun _ => 100 * cfg.regularOpCost + (40 * cfg.regularOpCost + costA cfg F c))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 32) 32 ∗ vt n 1057464 idx ta (A 578) ∗ heapS n maxP hl live F c p ∗
          block n p.toNat c.toNat ∗ n ↦[i32][ cur.toNat ] 0 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c)) := by
  iintro ⟨#Hcode, #H310, #H713⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha713 := hm.funcs 713 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_s c 0) = 1 := by
    have h' : c.toNat < 2147483648 := by omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hcur, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho4 with ⟨Ho4, Ho8⟩
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Lo, Fr⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Fr with ⟨F0, F8⟩
  iunfold stk at F0
  icases F0 with ⟨%f0, %hf0, F0⟩
  have key := f713_alloc (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (s - 16) (s - 16) c idx maxP hl live F f0 hf0 (by omega) (by omega) hc0 hc hr
  generalize hK : costA cfg F c = K at key ⊢
  rw [show 100 * cfg.regularOpCost + (40 * cfg.regularOpCost + K) + R =
    100 * cfg.regularOpCost + (40 * cfg.regularOpCost + K + R) by omega]
  ihave Lo := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ Lo
  ihave F0 := memBytes_addr (show s.toNat - 32 + 16 = (s - 16).toNat by omega) $$ F0
  unfold f714
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcur]
  mstep
  mstep_not_taken with (simp)
  repeat mstep
  mcall key using [Hg Lo Hvt Hinv F0]
  · iframe Hg Lo Hvt Hinv F0
  icases HQ with ⟨%hrs, %p, Hg, Lo, Hvt, HA, Hb, P0, P4⟩
  subst hrs
  clear key
  ihave HA := SerdeString.heapS_ne $$ HA
  icases HA with ⟨%hp0, HA⟩
  mcredits (48 * cfg.regularOpCost + R)
  repeat mstep
  mstep [P4]
  repeat mstep
  mstep [P0]
  repeat mstep
  repeat mstep
  mstep [Ho4]
  repeat mstep
  mstep [Ho0]
  repeat mstep
  mstep [Ho8]
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt HA Hb Hcur Ho0 Ho4 Ho8
  ihave Lo := stk_addr (show (s - 16).toNat - 16 = s.toNat - 32 by omega) $$ Lo
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave P := stk_join n (s - 16).toNat 4 4 $$ [P0 P4]
  · iframe P0 P4
  ihave P := stk_addr (show (s - 16).toNat = s.toNat - 32 + 16 by omega) $$ P
  ihave Fr := stk_join n (s.toNat - 32 + 16) 8 8 $$ [P F8]
  · iframe P F8
  iapply stk_join n (s.toNat - 32) 16 16
  iframe Lo Fr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The general reserve chain allocates its first buffer at `max(8, k)` from capacity and length zero. -/
theorem f716_alloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec k ptr idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (ob : List UInt8) (hs : 64 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hk : k.toNat < 2 ^ 28)
    (hr : roomFor hl maxP (VecGrow.growCap 0 k)) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 713 ↪[wf] FuncInst.wasm types[31]! inst f713 ∗ A 714 ↪[wf] FuncInst.wasm types[39]! inst f714 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f716 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 vec, .i32 0, .i32 k]⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 200 * cfg.regularOpCost + (100 * cfg.regularOpCost +
          (40 * cfg.regularOpCost + costA cfg F (VecGrow.growCap 0 k))))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] VecGrow.growCap 0 k ∗ n ↦[i32][ out.toNat ] 0 ∗
          heapS n maxP hl live F (VecGrow.growCap 0 k) p ∗ block n p.toNat (VecGrow.growCap 0 k).toNat)) := by
  iintro ⟨#HC, #F310, #F713, #F714⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at HC
    icases HC with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha714 := hm.funcs 714 (by decide)
  have t39 : types[39]!.params.length = 5 := rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have hgc := VecGrow.growCap_toNat 0 k (by simp)
  have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u k 8) = 0 then Value.i32 8 else Value.i32 k) =
      Value.i32 (VecGrow.growCap 0 k) := by
    by_cases h8 : 8 < k.toNat
    · have ht : Numeric.bool (Numeric.irelop32 IRelOp.gt_u k 8) = 1 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat]
        simp [h8]
      rw [ht]
      simp only [show (1 : UInt32) ≠ 0 by decide, ite_false, Value.i32.injEq]
      apply UInt32.toNat_inj.mp
      rw [hgc]
      simp; omega
    · have ht : Numeric.bool (Numeric.irelop32 IRelOp.gt_u k 8) = 0 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat]
        simp [h8]
      rw [ht]
      simp only [ite_true, Value.i32.injEq]
      apply UInt32.toNat_inj.mp
      rw [hgc]
      simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, H64, Hvt, Hheap, Hp, Hcap, Ho⟩
  subst ha
  icases stk_split n (s.toNat - 64) 32 32 $$ H64 with ⟨Lo, Fr⟩
  icases stk_split n (s.toNat - 64 + 32) 12 20 $$ Fr with ⟨O7, Fr⟩
  icases stk_split n (s.toNat - 64 + 32 + 12) 4 16 $$ Fr with ⟨G1, Fr⟩
  icases stk_split n (s.toNat - 64 + 32 + 12 + 4) 4 12 $$ Fr with ⟨C0, G2⟩
  iunfold stk at O7 C0
  icases O7 with ⟨%ob7, %hob7, O7⟩
  icases C0 with ⟨%cb, %hcb, C0⟩
  ihave O7 := memBytes_addr (show s.toNat - 64 + 32 = (s - 32).toNat by omega) $$ O7
  ihave C0 := memBytes_addr (show s.toNat - 64 + 32 + 12 + 4 = (s - 32 + 16).toNat by omega) $$ C0
  have key := f714_alloc (GF := GF) cfg lim (d + 1) types[39]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 32) (s - 32) (VecGrow.growCap 0 k) (s - 32 + 16) (s - 32) idx maxP hl live F ob7
    (by omega) hob7 (by omega) (by rw [hgc]; simp only [UInt32.toNat_zero, Nat.mul_zero]; omega) (by rw [hgc]; simp only [UInt32.toNat_zero, Nat.mul_zero]; omega) hr
  ihave #S714 := key $$ [HC F310 F713]
  · iframe HC F310 F713
  clear key
  unfold f716
  generalize hK : costA cfg F (VecGrow.growCap 0 k) = K
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post
  rw [show (UInt32.ofNat 0 : UInt32) = 0 from rfl,
    show (0 : UInt32) <<< (1 % 32) = 0 by decide, UInt32.zero_add]
  have hfirst : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u 0 k) = 0 then Value.i32 k else Value.i32 0) = Value.i32 k := by
    simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]
  rw [hfirst]
  clear hfirst
  repeat mstep
  iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post
  rw [hsel]
  repeat mstep
  mstep [C0]
  repeat mstep
  mcall S714 using [Hg Lo Hvt Hheap C0 O7]
  · ihave Lo := stk_addr (show s.toNat - 64 = (s - 32).toNat - 32 by omega) $$ Lo
    iframe Hg Lo Hvt Hheap C0 O7
  icases HQ with ⟨%hrs, %p, Hg, Lo, Hvt, HA, Hb, C0, Q0, Q4, Q8⟩
  subst hrs
  clear hK
  mcredits (60 * cfg.regularOpCost + R)
  repeat mstep
  mstep [Q8]
  repeat mstep
  mstep [Q4]
  repeat mstep
  mstep [Q0]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hp]
  repeat mstep
  mstep [Ho]
  repeat mstep
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Hp Hcap Ho HA Hb
  ihave Lo := stk_addr (show (s - 32).toNat - 32 = s.toNat - 64 by omega) $$ Lo
  ihave Q0 := stk_word n _ 0 $$ Q0
  ihave Q4 := stk_word n _ p $$ Q4
  ihave Q8 := stk_word n _ _ $$ Q8
  ihave C0 := stk_word n _ 0 $$ C0
  ihave Q := BorshFT.stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [Q0 Q4]
  · iframe Q0 Q4
  ihave Q := BorshFT.stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 8) (k1 := 8) (k2 := 4) (k := 12) rfl rfl $$ [Q Q8]
  · iframe Q Q8
  ihave Q := BorshFT.stkJ (a := (s - 32).toNat) (b := s.toNat - 64 + 32 + 12) (k1 := 12) (k2 := 4) (k := 16) (by omega) rfl $$ [Q G1]
  · iframe Q G1
  ihave C := stk_addr (show (s - 32 + 16).toNat = s.toNat - 16 by omega) $$ C0
  ihave C := stk_join n (s.toNat - 16) 4 12 $$ [C G2]
  · rw [show s.toNat - 16 + 4 = s.toNat - 64 + 32 + 12 + 4 + 4 by omega]
    iframe C G2
  ihave Q := BorshFT.stkJ (a := (s - 32).toNat) (b := s.toNat - 16) (k1 := 16) (k2 := 16) (k := 32) (by omega) rfl $$ [Q C]
  · iframe Q C
  iapply stk_join n (s.toNat - 64) 32 32
  rw [show s.toNat - 64 + 32 = (s - 32).toNat by omega]
  iframe Lo Q

/-- The concrete reserve chain reached by an ignored-frame push. -/
def code (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
    A 713 ↪[wf] FuncInst.wasm types[31]! inst f713 ∗ A 714 ↪[wf] FuncInst.wasm types[39]! inst f714 ∗
    A 716 ↪[wf] FuncInst.wasm types[45]! inst f716 ∗ A 715 ↪[wf] FuncInst.wasm types[45]! inst f715 ∗
    A 712 ↪[wf] FuncInst.wasm types[31]! inst f712 ∗ A 698 ↪[wf] FuncInst.wasm types[14]! inst f698)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code (GF := GF) n maxP inst mi A) := by
  unfold code; infer_instance

/-- An empty Vec descriptor with no live buffer allocation. -/
def pre (n g S : Nat) (gt : GlobalType) (s vec ptr idx : UInt32) (ta alloc maxP hl F : Nat)
    (live : List (Nat × Nat)) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗ vt n 1057464 idx ta alloc ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗
    n ↦[i32][ vec.toNat + 8 ] 0)

/-- Reservation installs one fresh allocation and preserves every previously live block. -/
def post (n g S : Nat) (gt : GlobalType) (s vec idx k : UInt32) (ta alloc maxP hl F : Nat)
    (live : List (Nat × Nat)) : IProp GF :=
  iprop(∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗ vt n 1057464 idx ta alloc ∗
    n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] VecGrow.growCap 0 k ∗
    n ↦[i32][ vec.toNat + 8 ] 0 ∗ heapS n maxP hl live F (VecGrow.growCap 0 k) p ∗
    block n p.toNat (VecGrow.growCap 0 k).toNat)

set_option maxRecDepth 100000 in
/-- The actual reserve check delegates an empty Vec's positive request to its first-allocation path. -/
theorem f715_alloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec k ptr idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (ob : List UInt8) (hs : 64 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hk0 : 0 < k.toNat) (hk : k.toNat < 2 ^ 28) (hr : roomFor hl maxP (VecGrow.growCap 0 k)) :
    code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f715 Cg
      (fun args => iprop(⌜args = [.i32 out, .i32 vec, .i32 0, .i32 k]⌝ ∗
        pre n g 64 gt s vec ptr idx ta (A 578) maxP hl F live ∗ n ↦[wms][ out.toNat ] ob))
      (fun _ => 380 * cfg.regularOpCost + costA cfg F (VecGrow.growCap 0 k))
      (fun _ rs => iprop(⌜rs = []⌝ ∗ post n g 64 gt s vec idx k ta (A 578) maxP hl F live ∗
        n ↦[i32][ out.toNat ] 0)) := by
  iintro #HC
  iunfold code at HC
  icases HC with ⟨#C310, #F310, #F713, #F714, #F716, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at C310
    icases C310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha716 := hm.funcs 716 (by decide)
  have t45 : types[45]!.params.length = 4 := rfl
  have hnot : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (0 - 0) k) = 0 := by
    simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
  have key := f716_alloc (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt
    s out vec k ptr idx maxP hl live F ob hs hob hout (by omega) hk hr
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, HP, Ho⟩
  iunfold pre at HP
  icases HP with ⟨Hg, Hs, Hvt, Hheap, Hp, Hcap, Hlen⟩
  subst ha
  unfold f715
  generalize hK : costA cfg F (VecGrow.growCap 0 k) = K at key ⊢
  mstep; mstep
  mstep [Hcap]
  repeat mstep
  mcall key using [Hg Hs Hvt Hheap Hp Hcap Ho] with (mstep_norm_full; simp only [Nat.add_mul]; omega)
  · iframe Hg Hs Hvt Hheap Hp Hcap Ho
  icases HQ with ⟨%hrs, %p, Hg, Hs, Hvt, Hp, Hcap, Ho, HA, Hb⟩
  subst hrs
  clear key hK hnot
  repeat mstep
  mcredits R
  iframe Hc Ho
  iunfold post
  iexists p
  iframe Hg Hs Hvt Hp Hcap Hlen HA Hb

set_option maxRecDepth 100000 in
/-- The reserve-and-handle wrapper returns a completely restored 80-byte frame after first allocation. -/
theorem f712_alloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec k ptr idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hs : 80 ≤ s.toNat) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hk0 : 0 < k.toNat) (hk : k.toNat < 2 ^ 28)
    (hr : roomFor hl maxP (VecGrow.growCap 0 k)) :
    code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f712 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 0, .i32 k]⌝ ∗ pre n g 80 gt s vec ptr idx ta (A 578) maxP hl F live))
      (fun _ => 440 * cfg.regularOpCost + costA cfg F (VecGrow.growCap 0 k))
      (fun _ rs => iprop(⌜rs = []⌝ ∗ post n g 80 gt s vec idx k ta (A 578) maxP hl F live)) := by
  iintro #HC
  ihave #HC' := HC
  iunfold code at HC'
  icases HC' with ⟨#C310, -, -, -, -, #F715, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at C310
    icases C310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha715 := hm.funcs 715 (by decide)
  have t45 : types[45]!.params.length = 4 := rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, HP⟩
  iunfold pre at HP
  icases HP with ⟨Hg, H80, Hvt, Hheap, Hp, Hcap, Hlen⟩
  subst ha
  icases stk_split n (s.toNat - 80) 64 16 $$ H80 with ⟨Lo, Fr⟩
  icases stk_split n (s.toNat - 80 + 64) 4 12 $$ Fr with ⟨O, U⟩
  iunfold stk at O
  icases O with ⟨%ob, %hob, O⟩
  ihave O := memBytes_addr (show s.toNat - 80 + 64 = (s - 16).toNat by omega) $$ O
  have key := f715_alloc (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 16) (s - 16) vec k ptr idx maxP hl live F ob (by rw [h16]; omega) hob (by omega) hvec hk0 hk hr
  unfold f712
  generalize hK : costA cfg F (VecGrow.growCap 0 k) = K at key ⊢
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall key using [Hg Lo Hvt Hheap Hp Hcap Hlen O]
  · iunfold pre
    ihave Lo := stk_addr (show s.toNat - 80 = (s - 16).toNat - 64 by omega) $$ Lo
    iframe Hg Lo Hvt Hheap Hp Hcap Hlen O
  icases HQ with ⟨%hrs, HQ, O⟩
  subst hrs
  clear key hK
  iunfold post at HQ
  icases HQ with ⟨%p, Hg, Lo, Hvt, Hp, Hcap, Hlen, HA, Hb⟩
  mcredits (20 * cfg.regularOpCost + R)
  repeat mstep
  mstep [O]
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iunfold post
  iexists p
  iframe Hg Hvt Hp Hcap Hlen HA Hb
  ihave Lo := stk_addr (show (s - 16).toNat - 64 = s.toNat - 80 by omega) $$ Lo
  ihave O := stk_word n _ 0 $$ O
  ihave O := stk_addr (show (s - 16).toNat = s.toNat - 80 + 64 by omega) $$ O
  ihave O := stk_join n (s.toNat - 80 + 64) 4 12 $$ [O U]
  · iframe O U
  iapply stk_join n (s.toNat - 80) 64 16
  iframe Lo O

set_option maxRecDepth 100000 in
/-- The concrete reserve reached by 84 allocates an empty Vec while keeping its length zero. -/
theorem f698_alloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec k ptr idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hs : 80 ≤ s.toNat) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hk0 : 0 < k.toNat) (hk : k.toNat < 2 ^ 28)
    (hr : roomFor hl maxP (VecGrow.growCap 0 k)) :
    code n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f698 Cg
      (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗ pre n g 80 gt s vec ptr idx ta (A 578) maxP hl F live))
      (fun _ => 480 * cfg.regularOpCost + costA cfg F (VecGrow.growCap 0 k))
      (fun _ rs => iprop(⌜rs = []⌝ ∗ post n g 80 gt s vec idx k ta (A 578) maxP hl F live)) := by
  iintro #HC
  ihave #HC' := HC
  iunfold code at HC'
  icases HC' with ⟨#C310, -, -, -, -, -, #F712, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at C310
    icases C310 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha712 := hm.funcs 712 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have key := f712_alloc (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
    s vec k ptr idx maxP hl live F hs hvec hk0 hk hr
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, HP⟩
  subst ha
  iunfold pre at HP
  icases HP with ⟨Hg, Hs, Hvt, Hheap, Hp, Hcap, Hlen⟩
  unfold f698
  generalize hK : costA cfg F (VecGrow.growCap 0 k) = K at key ⊢
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mcall key using [Hg Hs Hvt Hheap Hp Hcap Hlen]
  · iunfold pre
    iframe Hg Hs Hvt Hheap Hp Hcap Hlen
    ipureintro; rfl
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  clear key hK
  repeat mstep
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

end Proof
end WNear.Binary.VecGrowZero
