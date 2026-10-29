import Bridge.Functions.FmtSinkRe
import Bridge.Functions.StrSinkMulti
import Bridge.Functions.FmtString

/-!
# `to_string`'s `String` as a sink reallocated any number of times

`<T as ToString>::to_string` (470) starts from the empty `String` `(1, 0, 0)` and writes into it
through `fmt::write`'s `String` sink (759). A text of at most `B` bytes allocates it once and then
reallocates it while it does not fit: each growth at least doubles the capacity, the first gives at
least 8 bytes, so after `j` growths the capacity is at least `4·2^j`, and with `B ≤ 4·2^J` there are
at most `J` growths.

* `hsOk`: the facts after `j ≤ J` growths: the free-list bound between `F` and `F + j`, the memory at
  most `j` pages past `L0`, the capacity `0` (`j = 0`) or at least `4·2^j`, and at most `2B + 8`;
* `hsink`: the `String` `(ptr, cap, |w|)` at `v` holding the bytes `w` written so far, its block live
  on the heap once allocated (`liveOf`);
* `hsink_w`: `write_str` (759) of `k` bytes on `hsink`, `|w| + k ≤ B`: with room (`FmtSink.f759_room`),
  the first allocation (`FmtSink.f759_grow`) or a realloc (`FmtSinkRe.f759_re`), at `costHS` (the
  worst of the three); 112 bytes of stack.
-/

namespace WNear.Binary.HookSink

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen costAlloc)
open WNear.Binary.VecWithCap (okG costAllocF)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.VecGrow (reallocCode reallocated cost154 growCap growCap_toNat grownV)
open WNear.Binary.FmtSink (sinkCode roomPre roomPost growPre growPost strGrown grown f759_room f759_grow)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.FmtSinkRe (sinkCodeR growPreS growPostS f759_re costGrowS)
open WNear.Binary.StrSinkMulti (memcpy_mono)
open WNear.Binary.WriteSink (cellPages_one)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)
open WNear.Binary.SerdeStruct (MFunSpec_wrap)

/-- The live blocks: the `String`'s once allocated. -/
def liveOf (ptr cap : UInt32) (live : List (Nat × Nat)) : List (Nat × Nat) :=
  if cap.toNat = 0 then live else (ptr.toNat, cap.toNat) :: live

/-- The facts of `hsink` after `j ≤ J` growths. -/
def hsOk (L0 F J B : Nat) (ptr cap : UInt32) (hl F' : Nat) : Prop :=
  (∃ j, j ≤ J ∧ F ≤ F' ∧ F' ≤ F + j ∧ hl ≤ L0 + j * 65536 ∧
      (cap.toNat = 0 ∧ j = 0 ∨ 0 < j ∧ 4 * 2 ^ j ≤ cap.toNat)) ∧
    cap.toNat ≤ 2 * B + 8 ∧ hl % 65536 = 0 ∧ 0 < hl ∧ ptr ≠ 0 ∧ ptr.toNat + cap.toNat < 2 ^ 32

/-- The worst price of a write of `k` bytes on `hsink`. -/
noncomputable def costHS (cfg : WasmConfig) (F J B k : Nat) : Nat :=
  2000 * cfg.regularOpCost + MemCpy.cost k * cfg.regularOpCost + MemCpy.cost B * cfg.regularOpCost +
    AllocWalk.walkCost cfg (F + J) + cfg.linearOpBaseCost + cfg.linearOpUnitCost

/-- The global facts `hsink_w` needs. -/
structure HsGlobal (maxP L0 F J B : Nat) : Prop where
  hF : 1 ≤ F
  hJ : 1 ≤ J
  hBJ : B ≤ 4 * 2 ^ J
  hB : 2 * B + 8 ≤ 65000
  hL1 : L0 + (J + 1) * 65536 ≤ 2 ^ 32
  hL2 : L0 + J * 65536 ≤ maxP * 65536

theorem costAllocF_le (cfg : WasmConfig) {F F2 : Nat} (hF : F ≤ F2) (size : UInt32)
    (hs : size.toNat ≤ 65000) :
    costAllocF cfg F size ≤ 940 * cfg.regularOpCost + AllocWalk.walkCost cfg F2 + cfg.linearOpBaseCost +
      cfg.linearOpUnitCost := by
  have h1 := cellPages_one size hs
  have h2 := AllocWalk.wc_mono cfg hF
  unfold costAllocF
  split
  · simp only [costAlloc, AllocZeroed.cost581, h1, Bool.false_eq_true, ite_false, AllocWalk.walkCost]
    omega
  · simp only [AllocWalk.cost310W, AllocWalk.walkCost, h1]
    omega

theorem cost154_le' (cfg : WasmConfig) {F F2 B : Nat} {cap c : UInt32} (hF : F ≤ F2)
    (hc0 : 0 < cap.toNat) (hcB : cap.toNat ≤ B) (hc : c.toNat ≤ 65000) :
    cost154 cfg F cap c ≤ 914 * cfg.regularOpCost + AllocWalk.walkCost cfg F2 + cfg.linearOpBaseCost +
      cfg.linearOpUnitCost + MemCpy.cost B * cfg.regularOpCost := by
  have h1 := cellPages_one c hc
  have h2 := AllocWalk.wc_mono cfg hF
  have h3 := Nat.mul_le_mul_right cfg.regularOpCost (memcpy_mono hc0 hcB)
  simp only [cost154, AllocWalk.cost581W, AllocWalk.walkCost, h1]
  omega

theorem newCap_toNat (k : UInt32) (hk : k.toNat < 2 ^ 28) : (newCap 0 k).toNat = max k.toNat 8 := by
  unfold newCap; split <;> simp_all <;> omega

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`to_string`'s `String`** at `v` holding `w`, live on the heap once allocated, after at most
`J` growths. -/
def hsink (n maxP L0 : Nat) (live : List (Nat × Nat)) (F J B : Nat) (v idx : UInt32) (ta a578 : Nat)
    (w : List UInt8) : IProp GF :=
  iprop(vt n 1057464 idx ta a578 ∗ ∃ (ptr cap : UInt32) (hl F' : Nat) (rest : List UInt8),
    ⌜hsOk L0 F J B ptr cap hl F' ∧ w.length + rest.length = cap.toNat⌝ ∗
    n ↦[i32][ v.toNat ] ptr ∗ n ↦[i32][ v.toNat + 4 ] cap ∗ n ↦[i32][ v.toNat + 8 ] UInt32.ofNat w.length ∗
    n ↦[wms][ ptr.toNat ] (w ++ rest) ∗ heapInv n maxP hl (liveOf ptr cap live) F')

/-- The empty `String` `(1, 0, 0)` is `hsink []`. -/
theorem hsink_init (n maxP L0 : Nat) (live : List (Nat × Nat)) (F J B : Nat) (v idx : UInt32) (ta a578 : Nat)
    (hl : Nat) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) :
    vt (GF := GF) n 1057464 idx ta a578 ∗ n ↦[i32][ v.toNat ] 1 ∗ n ↦[i32][ v.toNat + 4 ] 0 ∗
      n ↦[i32][ v.toNat + 8 ] 0 ∗ heapInv n maxP hl live F ⊢
      hsink n maxP L0 live F J B v idx ta a578 [] := by
  iintro ⟨Hvt, V0, V4, V8, Hh⟩
  iunfold hsink
  iframe Hvt
  iexists 1, 0, hl, F, []
  isplitr
  · ipureintro
    refine ⟨⟨⟨0, by omega, le_rfl, by omega, by omega, Or.inl ⟨rfl, rfl⟩⟩, by simp, hl0, hl1, by decide,
      by decide⟩, by simp⟩
  iframe V0 V4
  isplitl [V8]
  · iexact V8
  isplitr
  · rw [List.append_nil]; iapply FmtString.memBytes_nil
  iunfold liveOf
  simp only [UInt32.reduceToNat, ite_true]
  iexact Hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **`write_str` (759) on `hsink`**: the `k` bytes `sb` at `p` appended to `w`, when
`|w| + k ≤ B`, with room, by the first allocation or through a realloc, at `costHS`; 112 bytes of
stack. -/
theorem hsink_w (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (maxP L0 : Nat) (live : List (Nat × Nat)) (F J B : Nat) (v idx : UInt32)
    (HG : HsGlobal maxP L0 F J B) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (s dd p k : UInt32) (w sb : List UInt8) (hs : 112 ≤ s.toNat) (hdd : dd.toNat + 4 ≤ 2 ^ 32)
    (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ B) :
    sinkCodeR n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f759 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[i32][ dd.toNat ] v ∗
          hsink n maxP L0 live F J B v idx ta (A 578) w ∗ n ↦[wms][ p.toNat ] sb))
        (fun _ => costHS cfg F J B k.toNat)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ n ↦[i32][ dd.toNat ] v ∗
          hsink n maxP L0 live F J B v idx ta (A 578) (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)) := by
  obtain ⟨hF1, hJ1, hBJ, hB, hL1, hL2⟩ := HG
  refine MFunSpec_wrap (α := UInt32 × UInt32 × Nat × Nat × List UInt8)
    (fun x => hsOk L0 F J B x.1 x.2.1 x.2.2.1 x.2.2.2.1 ∧ w.length + x.2.2.2.2.length = x.2.1.toNat)
    (P0 := fun x args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 112) 112 ∗ n ↦[i32][ dd.toNat ] v ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[i32][ v.toNat ] x.1 ∗ n ↦[i32][ v.toNat + 4 ] x.2.1 ∗
      n ↦[i32][ v.toNat + 8 ] UInt32.ofNat w.length ∗ n ↦[wms][ x.1.toNat ] (w ++ x.2.2.2.2) ∗
      heapInv n maxP x.2.2.1 (liveOf x.1 x.2.1 live) x.2.2.2.1 ∗ n ↦[wms][ p.toNat ] sb))
    (Q0 := fun _ _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
      n ↦[i32][ dd.toNat ] v ∗ hsink n maxP L0 live F J B v idx ta (A 578) (w ++ sb) ∗
      n ↦[wms][ p.toNat ] sb))
    (fun _ => iprop(emp)) ?_ ?_ ?_
  · rintro ⟨ptr, cap, hl, F', rest⟩ ⟨hok, hwr⟩
    simp only at hok hwr
    obtain ⟨⟨j, hjJ, hFF, hFj, hlj, hcj⟩, hcB, hl0, hl1, hp0, hpc⟩ := hok
    have hcap := cap.toNat_lt
    have hwl : (UInt32.ofNat w.length).toNat = w.length := by
      simp only [UInt32.toNat_ofNat']; omega
    by_cases hroom : w.length + k.toNat ≤ cap.toNat
    · -- with room
      have SW := f759_room (GF := GF) (maxP := maxP) cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt s
        dd v ptr cap (UInt32.ofNat w.length) p k (rest.take k.toNat) sb (by omega) (by simp; omega) hsb hdd hv
        (by omega) (by omega) hp
      refine (?_ : sinkCodeR (GF := GF) n maxP inst mi A ⊢ sinkCode n maxP inst mi A).trans
        (SW.trans ((MFunSpec_frame (Fr := iprop(stk n (s.toNat - 112) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP hl (liveOf ptr cap live) F' ∗ n ↦[wms][ ptr.toNat ] w ∗
          n ↦[wms][ ptr.toNat + w.length + k.toNat ] rest.drop k.toNat)) ?_ ?_).trans (MFunSpec_cost ?_)))
      · iintro #C
        iunfold sinkCodeR at C
        icases C with ⟨#C, -⟩
        iexact C
      · intro args
        iintro ⟨%ha, Hg, Hs, Hd, Hvt, V0, V4, V8, Hb, Hinv, Hsb⟩
        icases splitB (a := ptr.toNat) (b := ptr.toNat + w.length) w rest rfl $$ Hb with ⟨Hw, Hr⟩
        icases U128From.memBytes_split n (ptr.toNat + w.length) k.toNat rest (by omega) $$ Hr with ⟨Ho, Ht⟩
        icases stkSp 96 16 rfl $$ Hs with ⟨Hs1, Hs2⟩
        iframe Hs1 Hvt Hinv Hw Ht Hd
        isplitr
        · ipureintro; exact ha
        iunfold roomPre
        iframe Hg V0 V4 V8 Hsb
        isplitl [Hs2]
        · iapply stkA (by omega) $$ Hs2
        iapply memBytes_addr (show ptr.toNat + w.length = ptr.toNat + (UInt32.ofNat w.length).toNat by omega) $$ Ho
      · intro args rs
        iintro ⟨⟨Hs1, Hvt, Hinv, Hw, Ht⟩, %hrs, Hd, HQ⟩
        iunfold roomPost at HQ
        icases HQ with ⟨Hg, Hs2, V0, V4, V8, Ho, Hsb⟩
        iframe Hg Hd Hsb
        isplitr
        · ipureintro; exact hrs
        isplitl [Hs1 Hs2]
        · iapply stkJ (a := s.toNat - 112) (b := s.toNat - 16) (k1 := 96) (k2 := 16) (by omega) rfl
          iframe Hs1 Hs2
        iunfold hsink
        iframe Hvt
        iexists ptr, cap, hl, F', rest.drop k.toNat
        isplitr
        · ipureintro
          refine ⟨⟨⟨j, hjJ, hFF, hFj, hlj, hcj⟩, hcB, hl0, hl1, hp0, hpc⟩, ?_⟩
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
        have := Nat.zero_le (AllocWalk.walkCost cfg (F + J))
        simp only [costHS]
        omega
    · by_cases hc0 : cap.toNat = 0
      · -- the first allocation
        have hj0 : j = 0 := by
          rcases hcj with ⟨-, h⟩ | ⟨-, h⟩
          · exact h
          · have := Nat.one_le_two_pow (n := j); omega
        subst hj0
        have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hw0
        have hr0 : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hwr; omega)
        subst hr0
        have hk0 : 0 < k.toNat := by simp at hroom; omega
        have hFe : F' = F := by omega
        subst hFe
        have hcapz : cap = 0 := UInt32.toNat_inj.mp (by simp [hc0])
        subst hcapz
        have hnc := newCap_toNat k (by omega)
        have hP := cellPages_one (newCap 0 k) (by rw [hnc]; omega)
        have hr : roomFor hl maxP (newCap 0 k) := by
          refine ⟨hl0, hl1, ?_, ?_⟩ <;> rw [hP]
          · have := Nat.mul_le_mul_right 65536 hJ1; omega
          · have := Nat.mul_le_mul_right 65536 hJ1
            apply Nat.div_le_of_le_mul; omega
        have SG := f759_grow (GF := GF) cfg lim d type htype inst mi A n g ta hm (by omega) Cg gt s
          dd v ptr p k idx maxP hl live sb hs hsb hdd hv hk0 (by omega) hp hr F' hF1
        refine (?_ : sinkCodeR (GF := GF) n maxP inst mi A ⊢ sinkCode n maxP inst mi A).trans
          (SG.trans ((MFunSpec_frame (Fr := iprop(emp)) ?_ ?_).trans (MFunSpec_cost ?_)))
        · iintro #C
          iunfold sinkCodeR at C
          icases C with ⟨#C, -⟩
          iexact C
        · intro args
          iintro ⟨%ha, Hg, Hs, Hd, Hvt, V0, V4, V8, Hb, Hinv, Hsb⟩
          isplitl
          · iframe Hd
            isplitr
            · ipureintro; exact ha
            iunfold growPre
            iunfold liveOf at Hinv
            simp only [UInt32.reduceToNat, ite_true]
            iframe Hg Hs Hvt Hinv V0 V4 Hsb
            iexact V8
          · iempintro
        · intro args rs
          iintro ⟨-, %hrs, Hd, HQ⟩
          iunfold growPost at HQ
          icases HQ with ⟨Hg, Hs, Hvt, HG, Hsb⟩
          iunfold strGrown at HG
          icases HG with ⟨%q, %⟨hq0, hqb⟩, Q0, Q4, Q8, Hq, ⟨%tail, %htail, Ht⟩, HG⟩
          iunfold grown at HG
          icases HG with ⟨%hl', %hhl', Hinv⟩
          iframe Hg Hs Hd Hsb
          isplitr
          · ipureintro; exact hrs
          iunfold hsink
          simp only [List.nil_append]
          iframe Hvt
          iexists q, newCap 0 k, hl', F', tail
          isplitr
          · ipureintro
            refine ⟨⟨⟨1, hJ1, le_rfl, by omega, ?_, Or.inr ⟨by omega, by rw [hnc, show 4 * 2 ^ 1 = 8 from rfl]; omega⟩⟩,
              by rw [hnc]; omega, ?_, ?_, hq0, hqb⟩, by omega⟩
            · rcases hhl' with h | h
              · omega
              · rw [h]; simp only [grownLen]; rw [hP]; omega
            · rcases hhl' with h | h
              · omega
              · rw [h]; simp only [grownLen]; rw [hP]; omega
            · rcases hhl' with h | h
              · omega
              · rw [h]; simp only [grownLen]; omega
          iframe Q0 Q4
          isplitl [Q8]
          · iapply (show (n ↦[i32][ v.toNat + 8 ] k : IProp GF) ⊢
                n ↦[i32][ v.toNat + 8 ] UInt32.ofNat sb.length by
              rw [show UInt32.ofNat sb.length = k by
                apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_ofNat']; omega]) $$ Q8
          isplitl [Hq Ht]
          · iapply joinB (a := q.toNat) (b := q.toNat + sb.length) sb tail rfl
            iframe Hq
            iapply memBytes_addr (show q.toNat + k.toNat = q.toNat + sb.length by omega) $$ Ht
          iunfold liveOf
          have : (newCap 0 k).toNat ≠ 0 := by rw [hnc]; omega
          simp only [this, ite_false]
          iexact Hinv
        · intro _
          have := costAllocF_le cfg (F := F') (F2 := F' + J) (by omega) (newCap 0 k) (by rw [hnc]; omega)
          simp only [costHS]
          omega
      · -- a realloc: `cap < |w| + k ≤ B`, so fewer than `J` growths so far
        have hj0 : 0 < j ∧ 4 * 2 ^ j ≤ cap.toNat := by
          rcases hcj with ⟨h, -⟩ | h
          · exact absurd h hc0
          · exact h
        have hjJ' : j < J := by
          rcases Nat.lt_or_ge j J with h | h
          · exact h
          · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h; omega
        have hlive : (ptr.toNat, cap.toNat) ∈ liveOf ptr cap live := by
          simp [liveOf, hc0]
        have hwk : (UInt32.ofNat w.length + k).toNat = w.length + k.toNat := by
          rw [UInt32.toNat_add, hwl]; omega
        have hgc := growCap_toNat cap (UInt32.ofNat w.length + k) (by omega)
        rw [hwk] at hgc
        have hP := cellPages_one (growCap cap (UInt32.ofNat w.length + k)) (by rw [hgc]; omega)
        have hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k)) := by
          have : (j + 1) * 65536 ≤ J * 65536 := Nat.mul_le_mul_right 65536 hjJ'
          have e : (j + 1) * 65536 = j * 65536 + 65536 := Nat.succ_mul j 65536
          refine ⟨hl0, hl1, ?_, ?_⟩ <;> rw [hP]
          · omega
          · apply Nat.div_le_of_le_mul; omega
        have SG := f759_re (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt s dd v ptr cap p k
          idx maxP hl (liveOf ptr cap live) F' w rest sb hs hdd hv hp0 (by omega) (by omega) hwr hsb
          (by omega) (by omega) hp hlive hr
        refine SG.trans ((MFunSpec_frame (Fr := iprop(emp)) ?_ ?_).trans (MFunSpec_cost ?_))
        · intro args
          iintro ⟨%ha, Hg, Hs, Hd, Hvt, V0, V4, V8, Hb, Hinv, Hsb⟩
          isplitl
          · iframe Hd
            isplitr
            · ipureintro; exact ha
            iunfold growPreS
            iframe Hg Hs Hvt Hinv V0 V4 V8 Hb Hsb
          · iempintro
        · intro args rs
          iintro ⟨-, %hrs, Hd, HQ⟩
          iunfold growPostS at HQ
          icases HQ with ⟨%q, Hg, Hs, Hvt, Q0, Q4, Q8, Hq, ⟨%tail, %htail, Ht⟩, HG, Hsb⟩
          iunfold grownV at HG
          icases HG with ⟨%⟨hq0, hqb⟩, %hl', %hhl', Hinv⟩
          iframe Hg Hs Hd Hsb
          isplitr
          · ipureintro; exact hrs
          iunfold hsink
          iframe Hvt
          iexists q, growCap cap (UInt32.ofNat w.length + k), hl', max F' 1 + 1, tail
          have hel : (liveOf ptr cap live).erase (ptr.toNat, cap.toNat) = live := by simp [liveOf, hc0]
          rw [hel]
          have hgc0 : (growCap cap (UInt32.ofNat w.length + k)).toNat ≠ 0 := by rw [hgc]; omega
          iunfold liveOf
          simp only [hgc0, ite_false]
          iframe Q0 Q4 Q8 Hinv
          isplitr
          · ipureintro
            have hpw : 4 * 2 ^ (j + 1) = 2 * (4 * 2 ^ j) := by rw [Nat.pow_succ]; ring
            have e : (j + 1) * 65536 = j * 65536 + 65536 := Nat.succ_mul j 65536
            refine ⟨⟨⟨j + 1, by omega, by omega, by omega, ?_, Or.inr ⟨by omega, by rw [hpw, hgc]; omega⟩⟩,
              by rw [hgc]; omega, ?_, ?_, hq0, hqb⟩, by simpa using htail⟩
            · rcases hhl' with h | h
              · omega
              · rw [h]; simp only [grownLen]; rw [hP]; omega
            · rcases hhl' with h | h
              · omega
              · rw [h]; simp only [grownLen]; rw [hP]; omega
            · rcases hhl' with h | h
              · omega
              · rw [h]; simp only [grownLen]; omega
          iapply joinB (a := q.toNat) (b := q.toNat + (w ++ sb).length) (w ++ sb) tail rfl
          iframe Hq Ht
        · intro _
          simp only [costGrowS, costHS]
          have := cost154_le' cfg (F := F') (F2 := F + J) (B := B) (cap := cap) (by omega) (by omega) (by omega)
            (c := growCap cap (UInt32.ofNat w.length + k)) (by rw [hgc]; omega)
          omega
  · intro args
    iintro ⟨%ha, Hg, Hs, Hd, HS, Hsb⟩
    iunfold hsink at HS
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

end WNear.Binary.HookSink
