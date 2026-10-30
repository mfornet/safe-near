import Bridge.Functions.VecGrow
import Bridge.Functions.SerdeStruct

/-!
# `write_all` (345) on a sink: room or grow (M5)

`SerdeStruct`'s pieces write into `outV`, the serializer's `Vec<u8>` with room. When the output
outgrows the `Vec`'s capacity, one `write_all` reallocates it (`VecGrow.f345_grow`). Here the
two are put behind one interface, so the pieces above `write_all` can be proved once for both:

* `WaSpec C S B K`: a specification of 345's code on a *sink* `S : List UInt8 → IProp` (the bytes
  written so far): from any stack pointer with 80 bytes below it, `k` bytes `sb` at `p` appended
  to `S w`, `S (w ++ sb)`, when `|w| + k ≤ B`, at `K k`.
* `vsink`: the serializer's `Vec` with its heap, before or after one doubling of its capacity
  `c0`: `(ptr, c0)` live on `heapInv … F`, or `(q, 2·c0)` live on `heapInv … (max F 1 + 1)` (the
  realloc's alloc and free), the memory grown by at most a page past `L0`.
* `vsink_wa`: `WaSpec` for `vsink` with the bound `2·c0` and the cost `costW` (room or grow,
  the grow's price charged on every write).

Every method whose JSON outgrows the 128 bytes of the serializer's `Vec` (but not 256) writes
through `vsink`.
-/

namespace WNear.Binary.WriteSink

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages cellPages_toNat cellBytes_toNat)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.SerdeStruct (outV ofNat_len MFunSpec_wrap wa_out)
open WNear.Binary.VecGrow (waCode growCap growCap_toNat costGrow growPre growPost grownV f345_grow)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **A specification of `write_all` (345's code) on the sink `S`**, from the code `C`: `k` bytes
`sb` at `p` appended to `S w` when `|w| + k ≤ B`, at `K k`, from any stack pointer `s` with 80
bytes below it. -/
def WaSpec (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (n g : Nat)
    (gt : GlobalType) (C : IProp GF) (ser : UInt32) (S : List UInt8 → IProp GF) (B : Nat) (K : Nat → Nat) :
    Prop :=
  ∀ (d : Nat) (s p k : UInt32) (w sb : List UInt8), d + 16 < lim.maxCallDepth → 80 ≤ s.toNat →
    sb.length = k.toNat → p.toNat + k.toNat ≤ 2 ^ 32 → w.length + k.toNat ≤ B →
    C ⊢ MFunSpec cfg lim d types[31]! inst mi f345 Cg
      (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 80) 80 ∗ S w ∗ n ↦[wms][ p.toNat ] sb))
      (fun _ => K k.toNat)
      (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ S (w ++ sb) ∗
        n ↦[wms][ p.toNat ] sb))

/-- The facts of `vsink`: the capacity `c0` on the free-list bound `F` and the length `≤ L0`, or
the capacity `2·c0` after the realloc. -/
def vsinkOk (L0 F : Nat) (c0 ptr cap : UInt32) (hl F' : Nat) : Prop :=
  ((cap = c0 ∧ F' = F ∧ hl ≤ L0) ∨ (cap.toNat = 2 * c0.toNat ∧ F' = max F 1 + 1 ∧ hl ≤ L0 + 65536)) ∧
    hl % 65536 = 0 ∧ 0 < hl ∧ ptr ≠ 0

/-- **The serializer's `Vec` with its heap**: `*ser = vec`, the `Vec` `(ptr, cap, |w|)` holding
`w` (`outV`), live on the heap with `live`, before or after one doubling (`vsinkOk`). -/
def vsink (n maxP L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (ser vec c0 idx : UInt32) (ta a578 : Nat)
    (w : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ ser.toNat ] vec ∗ vt n 1057464 idx ta a578 ∗
    ∃ (ptr cap : UInt32) (hl F' : Nat), ⌜vsinkOk L0 F c0 ptr cap hl F'⌝ ∗ outV n vec ptr cap w ∗
      heapInv n maxP hl ((ptr.toNat, cap.toNat) :: live) F')

/-- The cost of a write on `vsink`: the grow's price on top of the room's. -/
def costW (cfg : WasmConfig) (F : Nat) (c0 : UInt32) (k : Nat) : Nat :=
  170 * cfg.regularOpCost + MemCpy.cost k * cfg.regularOpCost +
    costGrow cfg F c0 (UInt32.ofNat (2 * c0.toNat))

theorem cellPages_one (size : UInt32) (h : size.toNat ≤ 65000) : (cellPages (wordsOf size) 1).toNat = 1 := by
  have hw : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  rw [cellPages_toNat _ _ (by omega) (by decide), cellBytes_toNat _ _ (by omega) (by decide), hw]
  simp only [UInt32.reduceToNat]
  omega

theorem growCap_double {c0 x : UInt32} (h4 : 4 ≤ c0.toNat) (h26 : c0.toNat < 2 ^ 26)
    (hx : x.toNat ≤ 2 * c0.toNat) : growCap c0 x = UInt32.ofNat (2 * c0.toNat) := by
  apply UInt32.toNat_inj.mp
  rw [growCap_toNat c0 x (by omega), UInt32.toNat_ofNat']
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`write_all` on `vsink`**: with room, `SerdeStruct.wa_out`; without, the capacity `c0`
doubles (`VecGrow.f345_grow`). The bound is `2·c0`. -/
theorem vsink_wa (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType) (maxP L0 : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ser vec c0 idx : UInt32)
    (hc4 : 4 ≤ c0.toNat) (hc26 : 2 * c0.toNat ≤ 65000) (hL1 : L0 + 2 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 65536 ≤ maxP * 65536) (hser : ser.toNat + 4 ≤ 2 ^ 32) :
    WaSpec (GF := GF) cfg lim inst mi Cg n g gt (waCode n maxP inst mi A) ser
      (vsink n maxP L0 live F ser vec c0 idx ta (A 578)) (2 * c0.toNat) (costW cfg F c0) := by
  intro d s p k w sb hd hs hsb hp hB
  refine MFunSpec_wrap (α := UInt32 × UInt32 × Nat × Nat × List UInt8)
    (fun x => vsinkOk L0 F c0 x.1 x.2.1 x.2.2.1 x.2.2.2.1 ∧ w.length + x.2.2.2.2.length = x.2.1.toNat ∧
      x.1.toNat + x.2.1.toNat < 2 ^ 32 ∧ vec.toNat + 12 ≤ 2 ^ 32)
    (P0 := fun x args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 80) 80 ∗ n ↦[i32][ ser.toNat ] vec ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[i32][ vec.toNat ] x.1 ∗ n ↦[i32][ vec.toNat + 4 ] x.2.1 ∗
      n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat w.length ∗ n ↦[wms][ x.1.toNat ] (w ++ x.2.2.2.2) ∗
      heapInv n maxP x.2.2.1 ((x.1.toNat, x.2.1.toNat) :: live) x.2.2.2.1 ∗ n ↦[wms][ p.toNat ] sb))
    (Q0 := fun _ _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗
      vsink n maxP L0 live F ser vec c0 idx ta (A 578) (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb))
    (fun _ => iprop(emp)) ?_ ?_ ?_
  · rintro ⟨ptr, cap, hl, F', rest⟩ ⟨hok, hwr, hpc, hv⟩
    simp only at hok hwr hpc hv
    obtain ⟨hcase, hl0, hl1, hp0⟩ := hok
    have hcap := cap.toNat_lt
    by_cases hroom : w.length + k.toNat ≤ cap.toNat
    · -- with room
      have SW := wa_out (GF := GF) cfg lim d types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s ser vec
        ptr cap p k w sb (by omega) hsb hser hroom hp
      refine (?_ : waCode (GF := GF) n maxP inst mi A ⊢ VecAppend.appCode inst mi A).trans
        (SW.trans ((MFunSpec_frame (Fr := iprop(stk n (s.toNat - 80) 64 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP hl ((ptr.toNat, cap.toNat) :: live) F')) ?_ ?_).trans (MFunSpec_cost ?_)))
      · iintro #C; iunfold waCode at C; icases C with ⟨-, #H⟩; iexact H
      · intro args
        iintro ⟨%ha, Hg, Hs, Hser, Hvt, V0, V4, V8, Hb, Hinv, Hsb⟩
        icases stkSp 64 16 rfl $$ Hs with ⟨Lo, Hs⟩
        iframe Lo Hvt Hinv Hg Hser Hsb
        isplitr
        · ipureintro; exact ha
        isplitl [Hs]
        · iapply stkA (by omega) $$ Hs
        iunfold outV
        iexists rest
        iframe V0 V4 V8 Hb
        ipureintro; exact ⟨hwr, hpc, by omega⟩
      · intro args rs
        iintro ⟨⟨Lo, Hvt, Hinv⟩, %hrs, Hg, Hs, Hser, Ho, Hsb⟩
        iframe Hg Hsb
        isplitr
        · ipureintro; exact hrs
        isplitl [Lo Hs]
        · iapply stkJ (a := s.toNat - 80) (b := s.toNat - 16) (k1 := 64) (k2 := 16) (by omega) rfl
          iframe Lo Hs
        iunfold vsink
        iframe Hser Hvt
        iexists ptr, cap, hl, F'
        iframe Ho Hinv
        ipureintro; exact ⟨hcase, hl0, hl1, hp0⟩
      · intro _; unfold costW; omega
    · -- the grow: the capacity is `c0`
      have hc0 : cap = c0 := by
        rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · omega
      obtain ⟨-, hF', hlL⟩ : cap = c0 ∧ F' = F ∧ hl ≤ L0 := by
        rcases hcase with h | ⟨h, -⟩
        · exact h
        · omega
      subst hc0
      subst F'
      have hwl : (UInt32.ofNat w.length).toNat = w.length := by
        simp only [UInt32.toNat_ofNat']; omega
      have hwk : (UInt32.ofNat w.length + k).toNat = w.length + k.toNat := by
        rw [UInt32.toNat_add, hwl]; omega
      have hgc : growCap cap (UInt32.ofNat w.length + k) = UInt32.ofNat (2 * cap.toNat) :=
        growCap_double hc4 (by omega) (by omega)
      have hP := cellPages_one (UInt32.ofNat (2 * cap.toNat)) (by simp only [UInt32.toNat_ofNat']; omega)
      have hc2 : (UInt32.ofNat (2 * cap.toNat)).toNat = 2 * cap.toNat := by
        simp only [UInt32.toNat_ofNat']; omega
      have hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k)) := by
        rw [hgc]
        refine ⟨hl0, hl1, ?_, ?_⟩ <;> rw [hP] <;> omega
      have SG := f345_grow (GF := GF) cfg lim d types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s ser vec ptr
        cap p k idx maxP hl ((ptr.toNat, cap.toNat) :: live) F w rest sb hs hser hv hp0 (by omega) (by omega)
        hwr hsb (by omega) (by omega) hp (by simp) hr
      rw [hgc] at SG
      refine SG.trans ((MFunSpec_frame (Fr := iprop(emp)) ?_ ?_).trans (MFunSpec_cost ?_))
      · intro args
        iintro ⟨%ha, Hg, Hs, Hser, Hvt, V0, V4, V8, Hb, Hinv, Hsb⟩
        isplitl
        · iframe Hser
          isplitr
          · ipureintro; exact ha
          iunfold growPre
          iframe Hg Hs Hvt Hinv V0 V4 V8 Hb Hsb
        · iempintro
      · intro args rs
        iintro ⟨-, %hrs, Hser, HQ⟩
        iunfold growPost at HQ
        icases HQ with ⟨%q, Hg, Hs, Hvt, Q0, Q4, Q8, Hq, ⟨%tail, %htail, Ht⟩, HG, Hsb⟩
        iunfold grownV at HG
        icases HG with ⟨%⟨hq0, hqb⟩, %hl', %hhl', Hinv⟩
        iframe Hg Hs Hsb
        isplitr
        · ipureintro; exact hrs
        iunfold vsink
        iframe Hser Hvt
        iexists q, UInt32.ofNat (2 * cap.toNat), hl', max F 1 + 1
        have hel : ((ptr.toNat, cap.toNat) :: live).erase (ptr.toNat, cap.toNat) = live := by simp
        rw [hel]
        iframe Hinv
        isplitr
        · ipureintro
          refine ⟨Or.inr ⟨hc2, rfl, ?_⟩, ?_, ?_, hq0⟩
          · rcases hhl' with h | h
            · omega
            · rw [h]; simp only [grownLen]; rw [hP]; omega
          · rcases hhl' with h | h
            · rw [h]; exact hl0
            · rw [h]; simp only [grownLen]; omega
          · rcases hhl' with h | h
            · omega
            · rw [h]; simp only [grownLen]; omega
        iunfold outV
        iexists tail
        iframe Q0 Q4 Q8
        isplitr
        · ipureintro; exact ⟨by omega, hqb, hv⟩
        iapply joinB (a := q.toNat) (b := q.toNat + (w ++ sb).length) (w ++ sb) tail rfl
        iframe Hq Ht
      · intro _; unfold costW; omega
  · intro args
    iintro ⟨%ha, Hg, Hs, HS, Hsb⟩
    iunfold vsink at HS
    icases HS with ⟨Hser, Hvt, %ptr, %cap, %hl, %F', %hok, Ho, Hinv⟩
    iunfold outV at Ho
    icases Ho with ⟨%rest, %⟨h1, h2, h3⟩, V0, V4, V8, Hb⟩
    iexists (ptr, cap, hl, F', rest)
    isplitr
    · ipureintro; exact ⟨hok, h1, h2, h3⟩
    isplitl
    · iframe Hg Hs Hser Hvt V0 V4 V8 Hb Hinv Hsb
      ipureintro; exact ha
    · iempintro
  · intro x hx args rs
    iintro ⟨-, HQ⟩
    iexact HQ

end Spec

end WNear.Binary.WriteSink
