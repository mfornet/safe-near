import Bridge.Functions.StrSinkGrow
import Bridge.Functions.WriteSink

/-!
# `format!`'s `String` as a sink that may be reallocated twice (M8)

`alloc::fmt::format` (846) allocates its `String` with capacity `c0` (`2·L`, `L` the pieces'
total length) and writes into it through `write_str` (840). A text of at most `B ≤ 4·c0` bytes
reallocates it at most twice: each realloc at least doubles the capacity (`growCap`), and a
realloc only happens below `B`.

* `ssink`: the `String` `(ptr, cap, |w|)` at `v` holding the bytes `w` written so far, live on the
  heap, after `j ≤ 2` reallocs (`ssinkOk`): the free-list bound `fIt F j`, the memory grown by at most
  `j` pages past `L0`, the capacity at least `c0·2^j` and at most `c0 + 2B + 8`.
* `ssink_w`: `write_str` (840) of `k` bytes on `ssink`, `|w| + k ≤ B`, room (`StrSink.f840_room`)
  or grow (`StrSinkGrow.f840_grow`), at `costS` (the grow's worst price charged on every write).
-/

namespace WNear.Binary.StrSinkMulti

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.VecGrow (reallocCode reallocated cost154 growCap growCap_toNat grownV)
open WNear.Binary.StrSinkGrow (strCode gPre gPost f840_grow)
open WNear.Binary.SerdeStruct (MFunSpec_wrap)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)
open WNear.Binary.WriteSink (cellPages_one)

/-- The free-list bound after `j` reallocs. -/
def fIt (F : Nat) : Nat → Nat
  | 0 => F
  | j + 1 => max (fIt F j) 1 + 1

/-- The facts of `ssink` after `j ≤ 2` reallocs. -/
def ssinkOk (L0 F c0 B : Nat) (ptr cap : UInt32) (hl F' : Nat) : Prop :=
  (∃ j, j ≤ 2 ∧ F' = fIt F j ∧ hl ≤ L0 + j * 65536 ∧ c0 * 2 ^ j ≤ cap.toNat) ∧
    cap.toNat ≤ c0 + 2 * B + 8 ∧ hl % 65536 = 0 ∧ 0 < hl ∧ ptr ≠ 0 ∧ ptr.toNat + cap.toNat < 2 ^ 32

/-- The worst price of a realloc on `ssink`. -/
noncomputable def gmax (cfg : WasmConfig) (F B : Nat) : Nat :=
  80 * cfg.regularOpCost + (AllocWalk.walkCost cfg (max F 1 + 1) + 610 * cfg.regularOpCost +
    cfg.linearOpBaseCost + cfg.linearOpUnitCost * 1) + MemCpy.cost B * cfg.regularOpCost + 224 * cfg.regularOpCost

/-- The cost of a write of `k` bytes on `ssink`. -/
noncomputable def costS (cfg : WasmConfig) (F B k : Nat) : Nat :=
  10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f841 [.i32 0, .i32 0, .i32 0]) +
    (300 * cfg.regularOpCost + MemCpy.cost k * cfg.regularOpCost + gmax cfg F B)

theorem fIt_le_one (F : Nat) {j : Nat} (hj : j ≤ 1) : fIt F j ≤ max F 1 + 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h | h <;> subst h <;> simp [fIt] <;> omega

theorem memcpy_mono {a b : Nat} (h1 : 0 < a) (h : a ≤ b) : MemCpy.cost a ≤ MemCpy.cost b := by
  unfold MemCpy.cost; split <;> split <;> omega

theorem cost154_le (cfg : WasmConfig) {F F' B : Nat} {cap c : UInt32} (hF : F' ≤ max F 1 + 1)
    (hc0 : 0 < cap.toNat) (hcB : cap.toNat ≤ B) (hc : c.toNat ≤ 65000) :
    cost154 cfg F' cap c ≤ gmax cfg F B := by
  have h1 := cellPages_one c hc
  have h2 := AllocWalk.wc_mono cfg hF
  have h3 := Nat.mul_le_mul_right cfg.regularOpCost (memcpy_mono hc0 hcB)
  simp only [cost154, gmax, AllocWalk.cost581W, AllocWalk.walkCost, h1]
  omega

/-- `ssinkOk` after one more realloc. -/
theorem ssinkOk_grow {L0 F c0 B j hl hl' F' wk : Nat} {cap c q : UInt32} (hj1 : j ≤ 1) (hFj : F' = fIt F j)
    (hlj : hl ≤ L0 + j * 65536) (hcj : c0 * 2 ^ j ≤ cap.toNat)
    (hc : c.toNat = max (max (2 * cap.toNat) wk) 8) (hwk : wk ≤ B) (hcw : cap.toNat < wk)
    (hB : c0 + 2 * B + 8 ≤ 65000) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl)
    (hhl' : hl' = hl ∨ hl' = hl + 65536) (hq0 : q ≠ 0) (hqb : q.toNat + c.toNat < 2 ^ 32) :
    ssinkOk L0 F c0 B q c hl' (max F' 1 + 1) := by
  have hJ : (j + 1) * 65536 = j * 65536 + 65536 := Nat.succ_mul j 65536
  have hP : c0 * 2 ^ (j + 1) = 2 * (c0 * 2 ^ j) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_left_comm]
  refine ⟨⟨j + 1, by omega, by rw [hFj]; rfl, ?_, ?_⟩, ?_, ?_, ?_, hq0, hqb⟩
  · rw [hJ]; rcases hhl' with h | h <;> omega
  · rw [hP]; omega
  · omega
  · rcases hhl' with h | h <;> omega
  · rcases hhl' with h | h <;> omega

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`format!`'s `String`** at `v` holding `w`, live on the heap, after at most two reallocs. -/
def ssink (n maxP L0 : Nat) (live : List (Nat × Nat)) (F c0 B : Nat) (v idx : UInt32) (ta a578 : Nat)
    (w : List UInt8) : IProp GF :=
  iprop(vt n 1057464 idx ta a578 ∗ ∃ (ptr cap : UInt32) (hl F' : Nat) (rest : List UInt8),
    ⌜ssinkOk L0 F c0 B ptr cap hl F' ∧ w.length + rest.length = cap.toNat⌝ ∗
    n ↦[i32][ v.toNat ] ptr ∗ n ↦[i32][ v.toNat + 4 ] cap ∗ n ↦[i32][ v.toNat + 8 ] UInt32.ofNat w.length ∗
    n ↦[wms][ ptr.toNat ] (w ++ rest) ∗ heapInv n maxP hl ((ptr.toNat, cap.toNat) :: live) F')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`write_str` (840) on `ssink`**: the `k` bytes `sb` at `p` appended to `w`, when
`|w| + k ≤ B`, with room or through a realloc, at `costS`; 48 bytes of stack. -/
theorem ssink_w (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (maxP L0 : Nat) (live : List (Nat × Nat)) (F c0 B : Nat) (v idx : UInt32)
    (hc1 : 1 ≤ c0) (hB4 : B ≤ 4 * c0) (hB : c0 + 2 * B + 8 ≤ 65000) (hL1 : L0 + 3 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 2 * 65536 ≤ maxP * 65536) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (s dp p k : UInt32) (w sb : List UInt8) (hs : 48 ≤ s.toNat) (hsb : sb.length = k.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ B) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f840 Cg
        (fun args => iprop(⌜args = [.i32 dp, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
          ssink n maxP L0 live F c0 B v idx ta (A 578) w ∗ n ↦[wms][ p.toNat ] sb))
        (fun _ => costS cfg F B k.toNat)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
          ssink n maxP L0 live F c0 B v idx ta (A 578) (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)) := by
  refine MFunSpec_wrap (α := UInt32 × UInt32 × Nat × Nat × List UInt8)
    (fun x => ssinkOk L0 F c0 B x.1 x.2.1 x.2.2.1 x.2.2.2.1 ∧ w.length + x.2.2.2.2.length = x.2.1.toNat)
    (P0 := fun x args => iprop(⌜args = [.i32 dp, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[i32][ v.toNat ] x.1 ∗ n ↦[i32][ v.toNat + 4 ] x.2.1 ∗
      n ↦[i32][ v.toNat + 8 ] UInt32.ofNat w.length ∗ n ↦[wms][ x.1.toNat ] (w ++ x.2.2.2.2) ∗
      heapInv n maxP x.2.2.1 ((x.1.toNat, x.2.1.toNat) :: live) x.2.2.2.1 ∗ n ↦[wms][ p.toNat ] sb))
    (Q0 := fun _ _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗
      n ↦[i32][ dp.toNat ] v ∗ ssink n maxP L0 live F c0 B v idx ta (A 578) (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb))
    (fun _ => iprop(emp)) ?_ ?_ ?_
  · rintro ⟨ptr, cap, hl, F', rest⟩ ⟨hok, hwr⟩
    simp only at hok hwr
    obtain ⟨⟨j, hj2, hFj, hlj, hcj⟩, hcB, hl0, hl1, hp0, hpc⟩ := hok
    have hcap := cap.toNat_lt
    have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hcap0 : 0 < cap.toNat := by
      have := Nat.mul_le_mul hc1 hpow; omega
    by_cases hroom : w.length + k.toNat ≤ cap.toNat
    · -- with room
      have hwl : (UInt32.ofNat w.length).toNat = w.length := by
        simp only [UInt32.toNat_ofNat']; omega
      have SW := StrSink.f840_room (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt s dp v ptr
        cap (UInt32.ofNat w.length) p k (rest.take k.toNat) sb hv (by simp; omega) hsb (by omega) (by omega) hp
      refine (?_ : strCode (GF := GF) n maxP inst mi A ⊢ iprop(inst ↪[inst] mi ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
          A 841 ↪[wf] FuncInst.wasm types[31]! inst f841)).trans
        (SW.trans ((MFunSpec_frame (Fr := iprop(stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP hl ((ptr.toNat, cap.toNat) :: live) F' ∗ n ↦[wms][ ptr.toNat ] w ∗
          n ↦[wms][ ptr.toNat + w.length + k.toNat ] rest.drop k.toNat)) ?_ ?_).trans (MFunSpec_cost ?_)))
      · iintro #C
        iunfold strCode at C
        icases C with ⟨#HR, -, #H841⟩
        iunfold reallocCode at HR
        icases HR with ⟨#H, -, #H951, -⟩
        iunfold AllocTwo.code310 at H
        icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
        iframe Hi H951 H841
      · intro args
        iintro ⟨%ha, Hg, Hs, Hd, Hvt, V0, V4, V8, Hb, Hinv, Hsb⟩
        icases splitB (a := ptr.toNat) (b := ptr.toNat + w.length) w rest rfl $$ Hb with ⟨Hw, Hr⟩
        icases U128From.memBytes_split n (ptr.toNat + w.length) k.toNat rest (by omega) $$ Hr with ⟨Ho, Ht⟩
        iframe Hs Hvt Hinv Hw Ht Hd
        isplitr
        · ipureintro; exact ha
        iunfold StrSink.roomPre
        iframe Hg V0 V4 V8 Hsb
        iapply memBytes_addr (show ptr.toNat + w.length = ptr.toNat + (UInt32.ofNat w.length).toNat by omega) $$ Ho
      · intro args rs
        iintro ⟨⟨Hs, Hvt, Hinv, Hw, Ht⟩, %hrs, Hd, HQ⟩
        iunfold StrSink.roomPost at HQ
        icases HQ with ⟨Hg, V0, V4, V8, Ho, Hsb⟩
        iframe Hg Hs Hd Hsb
        isplitr
        · ipureintro; exact hrs
        iunfold ssink
        iframe Hvt
        iexists ptr, cap, hl, F', rest.drop k.toNat
        isplitr
        · ipureintro
          refine ⟨⟨⟨j, hj2, hFj, hlj, hcj⟩, hcB, hl0, hl1, hp0, hpc⟩, ?_⟩
          simp; omega
        iframe V0 V4 Hinv
        isplitl [V8]
        · iapply (show (n ↦[i32][ v.toNat + 8 ] (UInt32.ofNat w.length + k) : IProp GF) ⊢
              n ↦[i32][ v.toNat + 8 ] UInt32.ofNat (w ++ sb).length by
            rw [show UInt32.ofNat w.length + k = UInt32.ofNat (w ++ sb).length by
              apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hwl]
              simp only [UInt32.toNat_ofNat', List.length_append]; omega]) $$ V8
        ihave Ho := memBytes_addr (show ptr.toNat + (UInt32.ofNat w.length).toNat = ptr.toNat + w.length by omega) $$ Ho
        ihave Hws := joinB (a := ptr.toNat) (b := ptr.toNat + w.length) w sb rfl $$ [Hw Ho]
        · iframe Hw Ho
        iapply joinB (a := ptr.toNat) (b := ptr.toNat + w.length + k.toNat) (w ++ sb) (rest.drop k.toNat)
          (by simp; omega)
        iframe Hws Ht
      · intro _
        simp only [costS]
        omega
    · -- the grow: `cap < |w| + k ≤ B`, so at most one realloc so far
      have hj1 : j ≤ 1 := by
        rcases Nat.lt_or_ge j 2 with h | h
        · omega
        · have : j = 2 := by omega
          subst this
          simp at hcj; omega
      have hwl : (UInt32.ofNat w.length).toNat = w.length := by
        simp only [UInt32.toNat_ofNat']; omega
      have hwk : (UInt32.ofNat w.length + k).toNat = w.length + k.toNat := by
        rw [UInt32.toNat_add, hwl]; omega
      have hgc := growCap_toNat cap (UInt32.ofNat w.length + k) (by omega)
      rw [hwk] at hgc
      have hP := cellPages_one (growCap cap (UInt32.ofNat w.length + k)) (by rw [hgc]; omega)
      have hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k)) := by
        refine ⟨hl0, hl1, ?_, ?_⟩ <;> rw [hP]
        · have : j * 65536 ≤ 65536 := by
            have := Nat.mul_le_mul_right 65536 hj1; omega
          omega
        · have : j * 65536 ≤ 65536 := by
            have := Nat.mul_le_mul_right 65536 hj1; omega
          omega
      have SG := f840_grow (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt s dp v ptr cap p k
        idx maxP hl ((ptr.toNat, cap.toNat) :: live) F' w rest sb hs hv hp0 hcap0 (by omega) hwr hsb
        (by omega) (by omega) hp (by simp) hr
      refine SG.trans ((MFunSpec_frame (Fr := iprop(emp)) ?_ ?_).trans (MFunSpec_cost ?_))
      · intro args
        iintro ⟨%ha, Hg, Hs, Hd, Hvt, V0, V4, V8, Hb, Hinv, Hsb⟩
        isplitl
        · iframe Hd
          isplitr
          · ipureintro; exact ha
          iunfold gPre
          iframe Hg Hs Hvt Hinv V0 V4 V8 Hb Hsb
        · iempintro
      · intro args rs
        iintro ⟨-, %hrs, Hd, HQ⟩
        iunfold gPost at HQ
        icases HQ with ⟨%q, Hg, Hs, Hvt, Q0, Q4, Q8, Hq, ⟨%tail, %htail, Ht⟩, HG, Hsb⟩
        iunfold grownV at HG
        icases HG with ⟨%⟨hq0, hqb⟩, %hl', %hhl', Hinv⟩
        iframe Hg Hs Hd Hsb
        isplitr
        · ipureintro; exact hrs
        iunfold ssink
        iframe Hvt
        iexists q, growCap cap (UInt32.ofNat w.length + k), hl', max F' 1 + 1, tail
        have hel : ((ptr.toNat, cap.toNat) :: live).erase (ptr.toNat, cap.toNat) = live := by simp
        rw [hel]
        iframe Q0 Q4 Q8 Hinv
        isplitr
        · ipureintro
          refine ⟨ssinkOk_grow hj1 hFj hlj hcj hgc (by omega : w.length + k.toNat ≤ B) (by omega) hB hl0 hl1
            (by rcases hhl' with h | h
                · exact Or.inl h
                · right; rw [h]; simp only [grownLen]; rw [hP]) hq0 hqb, by simpa using htail⟩
        iapply joinB (a := q.toNat) (b := q.toNat + (w ++ sb).length) (w ++ sb) tail rfl
        iframe Hq Ht
      · intro _
        simp only [costS]
        have := cost154_le cfg (F := F) (B := B) (hFj ▸ fIt_le_one F hj1) hcap0 (by omega)
          (c := growCap cap (UInt32.ofNat w.length + k)) (by rw [hgc]; omega)
        omega
  · intro args
    iintro ⟨%ha, Hg, Hs, Hd, HS, Hsb⟩
    iunfold ssink at HS
    icases HS with ⟨Hvt, %ptr, %cap, %hl, %F', %rest, %⟨hok, hwr⟩, V0, V4, V8, Hb, Hinv⟩
    iexists (ptr, cap, hl, F', rest)
    isplitr
    · ipureintro; exact ⟨hok, hwr⟩
    isplitl
    · iframe Hg Hs Hd Hvt V0 V4 V8 Hb Hinv Hsb
      ipureintro; exact ha
    · iempintro
  · intro x hx args rs
    iintro ⟨-, HQ⟩
    iexact HQ

end Spec

end WNear.Binary.StrSinkMulti
