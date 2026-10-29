import Bridge.Functions.SerdeString
import Bridge.Functions.VecGrow

/-!
# The scratch `Vec<u8>` of `serde_json`'s reader grows (M6): `finish_grow` (627), `grow_amortized`
(631), `try_reserve` (630), `handle_reserve` (628), `reserve` (623, 589)

`parse_str` (646) copies the decoded bytes of an escaped string into the deserializer's scratch
`Vec<u8>`. The scratch starts empty with capacity 0 (`Vec::new`, the dangling pointer 1), so its
first growth allocates; the later ones reallocate. The chain is not `VecGrow`'s (716/714): the code
of 631 and 627 differs, and 627 takes both paths.

```wat
;; 589 reserve(v, k)                 623(v, v.len, k)
;; 623 reserve(v, len, k)            frame 16: 630(sp, v, len, k); handle_reserve(sp) (628)
;; 630 try_reserve(out, v, len, k)   cap - len ≥ k ⇒ out := Ok; else grow_amortized (631)
;; 631 grow_amortized(out, v, len, k) frame 48: c := max(2·cap, len + k, 8); layout (608);
;;                                   cap = 0 ⇒ current memory None, else Some(ptr, cap, 1);
;;                                   finish_grow(sp+16, c, 1, sp+32, sp) (627); Ok(p, c) ⇒ v := (p, c)
;; 627 finish_grow(out, c, 1, cur, _) frame 16: cur = None ⇒ Global::allocate(c, 1) (624);
;;                                   cur = Some(ptr, cap), cap ≠ 0 ⇒ __rust_realloc (312)
;; 628 handle_reserve(r)             Ok ⇒ return
```
-/

namespace WNear.Binary.ScratchGrow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeString (heapS costA strCode)
open WNear.Binary.VecGrow (reallocCode reallocated preR postR post154 cost154 growCap growCap_toNat)

/-! ## `finish_grow` (627) -/

section L627

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`finish_grow(out, c, 1, cur, _)`** (627) with no current memory (`cur.ptr = 0`):
`Global::allocate(c, 1)` (624), `Ok((p, c))` at `out`. -/
theorem f627_alloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c cur x : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (ob : List UInt8) (hs : 48 ≤ s.toNat) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hc0 : 0 < c.toNat) (hc : c.toNat < 2 ^ 28) (hr : roomFor hl maxP c) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 625 ↪[wf] FuncInst.wasm types[45]! inst f625 ∗ A 624 ↪[wf] FuncInst.wasm types[31]! inst f624
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f627 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 c, .i32 1, .i32 cur, .i32 x]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗
          n ↦[i32][ cur.toNat ] 0 ∗ n ↦[wms][ out.toNat ] ob))
        (fun _ => 80 * cfg.regularOpCost + (70 * cfg.regularOpCost + costA cfg F c))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapS n maxP hl live F c p ∗
          block n p.toNat c.toNat ∗ n ↦[i32][ cur.toNat ] 0 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c)) := by
  iintro ⟨#Hcode, #H310, #H625, #H624⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha624 := hm.funcs 624 (by decide)
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
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs with ⟨Lo, Fr⟩
  icases stk_split n (s.toNat - 48 + 32) 8 8 $$ Fr with ⟨F0, F8⟩
  iunfold stk at F0
  icases F0 with ⟨%f0, %hf0, F0⟩
  have key := SerdeString.f624_s (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (s - 16) (s - 16) c idx maxP hl live F f0 hf0 (by omega) (by omega) hc (fun _ => hr)
  generalize hK : costA cfg F c = K at key ⊢
  rw [show 80 * cfg.regularOpCost + (70 * cfg.regularOpCost + K) + R =
    80 * cfg.regularOpCost + (70 * cfg.regularOpCost + K + R) by omega]
  ihave Lo := stk_addr (show s.toNat - 48 = (s - 16).toNat - 32 by omega) $$ Lo
  ihave F0 := memBytes_addr (show s.toNat - 48 + 32 = (s - 16).toNat by omega) $$ F0
  simp only [f627]
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
  ihave Lo := stk_addr (show (s - 16).toNat - 32 = s.toNat - 48 by omega) $$ Lo
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave P := stk_join n (s - 16).toNat 4 4 $$ [P0 P4]
  · iframe P0 P4
  ihave P := stk_addr (show (s - 16).toNat = s.toNat - 48 + 32 by omega) $$ P
  ihave Fr := stk_join n (s.toNat - 48 + 32) 8 8 $$ [P F8]
  · iframe P F8
  iapply stk_join n (s.toNat - 48) 32 16
  iframe Lo Fr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`finish_grow(out, c, 1, cur, _)`** (627) with the current memory `Some(ptr, cap)`, `cap ≠ 0`:
`__rust_realloc(ptr, cap, 1, c)` (312), `Ok((p, c))` at `out`. -/
theorem f627_realloc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c cur x ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (bs ob : List UInt8) (hs : 48 ≤ s.toNat) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcc : cap.toNat < c.toNat)
    (hc : c.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat) (hlive : (ptr.toNat, cap.toNat) ∈ live)
    (hr : roomFor hl maxP c) :
    reallocCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f627 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 c, .i32 1, .i32 cur, .i32 x]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗
          n ↦[i32][ cur.toNat ] ptr ∗ n ↦[i32][ cur.toNat + 4 ] cap ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 80 * cfg.regularOpCost + (40 * cfg.regularOpCost + cost154 cfg F cap c))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ cur.toNat ] ptr ∗ n ↦[i32][ cur.toNat + 4 ] cap ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          reallocated n maxP hl live F ptr cap c p bs)) := by
  iintro #Hk
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  ihave #S312 := VecGrow.f312_spec (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 16) ptr cap c idx maxP hl live F bs (by omega) hcap hcc hc hbs hlive hr $$ Hk
  iunfold reallocCode at Hk
  icases Hk with ⟨#H, -, -, -, -, #H312⟩
  iunfold code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha312 := hm.funcs 312 (by decide)
  have t33 : types[33]!.params.length = 4 := by rfl
  have hcap0 : cap ≠ 0 := by intro h; subst h; simp at hcap
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_s c 0) = 1 := by
    have h' : c.toNat < 2147483648 := by omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  generalize hK : cost154 cfg F cap c = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp, Hcap, Hbs, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho4 with ⟨Ho4, Ho8⟩
  icases stk_split n (s.toNat - 48) 16 32 $$ Hs with ⟨Un, Lo⟩
  icases stk_split n (s.toNat - 48 + 16) 16 16 $$ Lo with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 48 + 16 = (s - 16).toNat - 16 by omega) $$ Lo
  rw [show 80 * cfg.regularOpCost + (40 * cfg.regularOpCost + K) + R =
    80 * cfg.regularOpCost + (40 * cfg.regularOpCost + K + R) by omega]
  simp only [f627]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hp]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mcall S312 using [Hg Lo Hvt Hinv Hbs]
  · iunfold preR
    iframe Hg Lo Hvt Hinv Hbs
  iunfold post154 at HQ
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  iunfold postR at HQ
  icases HQ with ⟨Hg, Lo, Hvt, HA⟩
  iunfold reallocated at HA
  icases HA with ⟨%⟨hp0, hpb⟩, HA⟩
  mcredits (42 * cfg.regularOpCost + R)
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
  iframe Hg Hvt Hp Hcap Ho0 Ho4 Ho8
  isplitl [Un Lo Fr]
  · ihave Lo := stk_addr (show (s - 16).toNat - 16 = s.toNat - 48 + 16 by omega) $$ Lo
    ihave Lo := stk_join n (s.toNat - 48 + 16) 16 16 $$ [Lo Fr]
    · iframe Lo Fr
    iapply stk_join n (s.toNat - 48) 16 32
    iframe Un Lo
  iunfold reallocated
  iframe HA
  ipureintro; exact ⟨hp0, hpb⟩

end L627

/-! ## The scratch buffer, and `grow_amortized` (631) -/

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The scratch's buffer `(ptr, cap)` holding `bs`, then `cap - |bs|` bytes of junk, and the heap
with it: no block when `cap = 0` (the dangling pointer 1), else the block `(ptr, cap)` lent. -/
def sbuf (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ptr cap : UInt32) (bs : List UInt8) :
    IProp GF :=
  iprop(⌜bs.length ≤ cap.toNat ∧ ptr ≠ 0 ∧ ptr.toNat + cap.toNat < 2 ^ 32 ∧ (cap = 0 → ptr = 1)⌝ ∗
    n ↦[wms][ ptr.toNat ] bs ∗
    (∃ junk : List UInt8, ⌜junk.length = cap.toNat - bs.length⌝ ∗ n ↦[wms][ ptr.toNat + bs.length ] junk) ∗
    heapInv n maxP hl (if cap = 0 then live else (ptr.toNat, cap.toNat) :: live) F)

/-- The code of the scratch's growth (persistent). -/
def sgCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(strCode n maxP inst mi A ∗ reallocCode n maxP inst mi A ∗
    A 627 ↪[wf] FuncInst.wasm types[39]! inst f627 ∗ A 631 ↪[wf] FuncInst.wasm types[45]! inst f631 ∗
    A 630 ↪[wf] FuncInst.wasm types[45]! inst f630 ∗ A 628 ↪[wf] FuncInst.wasm types[0]! inst f628 ∗
    A 623 ↪[wf] FuncInst.wasm types[31]! inst f623 ∗ A 589 ↪[wf] FuncInst.wasm types[14]! inst f589 ∗
    A 588 ↪[wf] FuncInst.wasm types[31]! inst f588 ∗ A 613 ↪[wf] FuncInst.wasm types[31]! inst f613 ∗
    A 614 ↪[wf] FuncInst.wasm types[14]! inst f614)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (sgCode (GF := GF) n maxP inst mi A) := by
  unfold sgCode; infer_instance

end Defs

/-- The cost of growing the scratch from `cap` to `c`: an allocation (`cap = 0`) or a realloc. -/
def costGrow (cfg : WasmConfig) (F : Nat) (cap c : UInt32) : Nat :=
  200 * cfg.regularOpCost +
    if cap = 0 then 150 * cfg.regularOpCost + costA cfg F c else 120 * cfg.regularOpCost + cost154 cfg F cap c

theorem heapInv_pos {GF : BundledGFunctors} [WasmGS NearState GF] {n maxP hl : Nat} {a b : List (Nat × Nat)}
    {F : Nat} {p : Prop} [Decidable p] (h : p) :
    heapInv (GF := GF) n maxP hl (if p then a else b) F ⊢ heapInv n maxP hl a F := by
  rw [if_pos h]

theorem heapInv_neg {GF : BundledGFunctors} [WasmGS NearState GF] {n maxP hl : Nat} {a b : List (Nat × Nat)}
    {F : Nat} {p : Prop} [Decidable p] (h : ¬p) :
    heapInv (GF := GF) n maxP hl (if p then a else b) F ⊢ heapInv n maxP hl b F := by
  rw [if_neg h]

/-- 631's frame put back together: 48 bytes below it, then 8, then ten words. -/
theorem join631 {GF : BundledGFunctors} [WasmGS NearState GF] (n B : Nat) :
    stk (GF := GF) n B 48 ∗ stk n (B + 48) 8 ∗ stk n (B + 56) 4 ∗ stk n (B + 60) 4 ∗ stk n (B + 64) 4 ∗
      stk n (B + 68) 4 ∗ stk n (B + 72) 4 ∗ stk n (B + 76) 4 ∗ stk n (B + 80) 4 ∗ stk n (B + 84) 4 ∗
      stk n (B + 88) 4 ∗ stk n (B + 92) 4 ⊢ stk n B 96 := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11⟩
  ihave H := BorshFT.stkJ (a := B) (b := B + 48) (k1 := 48) (k2 := 8) (k := 56) rfl rfl $$ [H0 H1]
  · iframe H0 H1
  ihave H := BorshFT.stkJ (a := B) (b := B + 56) (k1 := 56) (k2 := 4) (k := 60) rfl rfl $$ [H H2]
  · iframe H H2
  ihave H := BorshFT.stkJ (a := B) (b := B + 60) (k1 := 60) (k2 := 4) (k := 64) rfl rfl $$ [H H3]
  · iframe H H3
  ihave H := BorshFT.stkJ (a := B) (b := B + 64) (k1 := 64) (k2 := 4) (k := 68) rfl rfl $$ [H H4]
  · iframe H H4
  ihave H := BorshFT.stkJ (a := B) (b := B + 68) (k1 := 68) (k2 := 4) (k := 72) rfl rfl $$ [H H5]
  · iframe H H5
  ihave H := BorshFT.stkJ (a := B) (b := B + 72) (k1 := 72) (k2 := 4) (k := 76) rfl rfl $$ [H H6]
  · iframe H H6
  ihave H := BorshFT.stkJ (a := B) (b := B + 76) (k1 := 76) (k2 := 4) (k := 80) rfl rfl $$ [H H7]
  · iframe H H7
  ihave H := BorshFT.stkJ (a := B) (b := B + 80) (k1 := 80) (k2 := 4) (k := 84) rfl rfl $$ [H H8]
  · iframe H H8
  ihave H := BorshFT.stkJ (a := B) (b := B + 84) (k1 := 84) (k2 := 4) (k := 88) rfl rfl $$ [H H9]
  · iframe H H9
  ihave H := BorshFT.stkJ (a := B) (b := B + 88) (k1 := 88) (k2 := 4) (k := 92) rfl rfl $$ [H H10]
  · iframe H H10
  iapply BorshFT.stkJ (a := B) (b := B + 92) (k1 := 92) (k2 := 4) (k := 96) rfl rfl
  iframe H H11

theorem heapS_pos {GF : BundledGFunctors} [WasmGS NearState GF] {n maxP hl : Nat} {live : List (Nat × Nat)}
    {F : Nat} {c p : UInt32} (h : c ≠ 0) :
    heapS (GF := GF) n maxP hl live F c p ⊢ ⌜p ≠ 0 ∧ p.toNat + c.toNat < 2 ^ 32⌝ ∗
      ∃ hl', ⌜hl' = hl ∨ hl' = grownLen hl c⌝ ∗ heapInv n maxP hl' ((p.toNat, c.toNat) :: live) (max F 1) := by
  unfold heapS; rw [if_neg h]

theorem memBytes_nil {GF : BundledGFunctors} [WasmGS NearState GF] (n a : Nat) :
    ⊢ (n ↦[wms][ a ] ([] : List UInt8) : IProp GF) := by
  unfold WasmLogic.memBytes; simp only [byteCells]; exact BigSepL.bigSepL_nil.2

section L631

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`grow_amortized(out, vec, len, k)`** (631) when the `k` bytes do not fit: the capacity
`c = growCap cap (len + k)`, allocated (`cap = 0`, 627 → 624) or reallocated (627 → 312); `Ok` at
`out`, the vector `(p, c)` holding the same bytes. -/
theorem f631_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (hs : 96 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hlen : len.toNat = bs.length)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : len.toNat + k.toNat < 2 ^ 27) (hfit : cap.toNat < len.toNat + k.toNat)
    (hr : roomFor hl maxP (growCap cap (len + k))) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f631 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => costGrow cfg F cap (growCap cap (len + k)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat), ⌜hl' = hl ∨ hl' = grownLen hl (growCap cap (len + k))⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] growCap cap (len + k) ∗
          n ↦[i32][ out.toNat ] 0 ∗ sbuf n maxP hl' live (F + 2) p (growCap cap (len + k)) bs)) := by
  have hlk' : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
  have hgc := growCap_toNat cap (len + k) (by omega)
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, #HR, #H627, -, -, -, -, -, -, -, -⟩
  ihave #HS' := HS
  iunfold strCode at HS'
  icases HS' with ⟨#Hcode, #H310, #H625, #H624, #H607, #H608, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha627 := hm.funcs 627 (by decide)
  have ha608 := hm.funcs 608 (by decide)
  have t39 : types[39]!.params.length = 5 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 48 + 8 := by simp [UInt32.toNat_add, h48]; omega
  have e16 : (s - 48 + 16).toNat = s.toNat - 48 + 16 := by simp [UInt32.toNat_add, h48]; omega
  have e32 : (s - 48 + 32).toNat = s.toNat - 48 + 32 := by simp [UInt32.toNat_add, h48]; omega
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (len + k) len) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']
  have hsh : (cap <<< (1 % 32)).toNat = 2 * cap.toNat := by
    simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hsel1 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (len + k)) = 0
      then Value.i32 (len + k) else Value.i32 (cap <<< (1 % 32))) =
      Value.i32 (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) := by
    by_cases h2 : len.toNat + k.toNat < 2 * cap.toNat
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (len + k)) = 1 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']; omega
      rw [this]; simp only [show (1 : UInt32) ≠ 0 by decide, ite_false, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hsh, UInt32.toNat_ofNat']; omega
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (len + k)) = 0 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']; omega
      rw [this]; simp only [ite_true, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hlk', UInt32.toNat_ofNat']; omega
  have hsel2 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u
      (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) 8) = 0
      then Value.i32 8 else Value.i32 (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat)))) =
      Value.i32 (growCap cap (len + k)) := by
    have hm' : (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))).toNat =
        max (2 * cap.toNat) (len.toNat + k.toNat) := by
      rw [UInt32.toNat_ofNat']; omega
    by_cases h8 : 8 < max (2 * cap.toNat) (len.toNat + k.toNat)
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u
          (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) 8) = 1 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, hm']
        simp; omega
      rw [this]; simp only [show (1 : UInt32) ≠ 0 by decide, ite_false, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hgc, hm']; omega
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u
          (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) 8) = 0 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, hm']
        simp; omega
      rw [this]; simp only [ite_true, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hgc]; simp; omega
  generalize hc : growCap cap (len + k) = c at hgc hsel2 hr ⊢
  have hc8 : 8 ≤ c.toNat := by omega
  have hc28 : c.toNat < 2 ^ 28 := by omega
  unfold costGrow
  generalize hX : (if cap = 0 then 150 * cfg.regularOpCost + costA cfg F c else 120 * cfg.regularOpCost + cost154 cfg F cap c) = X
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hsb, Ho⟩
  rw [show 200 * cfg.regularOpCost + X + R = 200 * cfg.regularOpCost + (X + R) by omega]
  subst hargs
  iunfold sbuf at Hsb
  icases Hsb with ⟨%⟨hbl, hp0, hpc, hp1⟩, Hbs, Hj, Hinv⟩
  icases stk_split n (s.toNat - 96) 32 64 $$ Hs with ⟨Lo, Hs⟩
  icases stk_split n (s.toNat - 96 + 32) 16 48 $$ Hs with ⟨L16, Fr⟩
  icases stk_split n (s.toNat - 96 + 32 + 16) 8 40 $$ Fr with ⟨U0, Fr⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8) 8 32 $$ Fr with ⟨Ls, Fr⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8) 12 20 $$ Fr with ⟨Os, Fr⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12) 4 16 $$ Fr with ⟨U1, Fr⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4) 4 12 $$ Fr with ⟨C0, Fr⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4) 4 8 $$ Fr with ⟨C4, Fr⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 + 4) 4 4 $$ Fr with ⟨C8, U2⟩
  iunfold stk at Ls Os C0 C4 C8
  icases Ls with ⟨%lb, %hlb, Ls⟩
  icases Os with ⟨%obo, %hobo, Os⟩
  icases C0 with ⟨%c0, %hc0, C0⟩
  icases C4 with ⟨%c4, %hc4, C4⟩
  icases C8 with ⟨%c8, %hc8', C8⟩
  ihave Ls := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 = (s - 48 + 8).toNat by omega) $$ Ls
  ihave Os := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 = (s - 48 + 16).toNat by omega) $$ Os
  ihave C0 := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 = (s - 48 + 32).toNat by omega) $$ C0
  ihave C4 := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 = (s - 48).toNat + 36 by omega) $$ C4
  ihave C8 := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 + 4 = (s - 48).toNat + 40 by omega) $$ C8
  ihave L16 := stk_addr (show s.toNat - 96 + 32 = (s - 48).toNat - 16 by omega) $$ L16
  simp only [f631]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post
  simp only [hsel1]
  repeat mstep
  iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post
  simp only [hsel2]
  mcall (SerdeString.f608_s cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 8) c lb hlb (by omega)) using [Hg L16 Ls]
  · iunfold VecFromElem.pre685
    iframe Hg L16 Ls
    ipureintro; rfl
  iunfold VecFromElem.post685 at HQ
  icases HQ with ⟨%hrs, Hg, L16, L0, L4⟩
  subst hrs
  ihave L0 := memBytes_addr (show (s - 48 + 8).toNat = (s - 48).toNat + 8 by omega) $$ L0
  ihave L4 := memBytes_addr (show (s - 48 + 8).toNat + 4 = (s - 48).toNat + 12 by omega) $$ L4
  ihave Lo := stk_join n (s.toNat - 96) 32 16 $$ [Lo L16]
  · ihave L16 := stk_addr (show (s - 48).toNat - 16 = s.toNat - 96 + 32 by omega) $$ L16
    iframe Lo L16
  ihave Lo := stk_addr (show s.toNat - 96 = (s - 48).toNat - 48 by omega) $$ Lo
  mstep; mstep [L4]; mstep; mstep; mstep [L0]; mstep
  by_cases hc0 : cap = 0
  · -- the first growth: no current memory, an allocation
    subst hc0
    have hb0 : bs = [] := by cases bs with | nil => rfl | cons _ _ => simp at hbl
    subst hb0
    ihave Hinv := heapInv_pos (show (0 : UInt32) = 0 from rfl) $$ Hinv
    have key := f627_alloc (GF := GF) cfg lim (d + 1) types[39]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 16) c (s - 48 + 32) (s - 48) idx maxP hl live F obo (by omega) hobo (by omega) (by omega) hc28 hr
    rw [if_pos rfl] at hX
    subst hX
    generalize hK : costA cfg F c = K at key ⊢
    repeat mstep
    mstep [Hcap]
    repeat mstep
    mstep [C0]
    repeat mstep
    mcall key using [Hg Lo Hvt Hinv C0 Os]
    · iframe Hg Lo Hvt Hinv C0 Os
      ipureintro; rfl
    clear key
    icases HQ with ⟨%hrs, %p, Hg, Lo, Hvt, HA, Hb, C0, O0, O4, O8⟩
    subst hrs
    ihave O4 := memBytes_addr (show (s - 48 + 16).toNat + 4 = (s - 48).toNat + 20 by omega) $$ O4
    ihave O0 := memBytes_addr (show (s - 48 + 16).toNat = (s - 48).toNat + 16 by omega) $$ O0
    mcredits (40 * cfg.regularOpCost + R)
    repeat mstep
    mstep [O8] with (simp [UInt32.toNat_add]; omega)
    repeat mstep
    mstep [O4]
    repeat mstep
    mstep [O0]
    repeat mstep
    mstep [Hcap]
    repeat mstep
    mstep [Hp]
    repeat mstep
    mstep [Ho]
    repeat mstep
    mstep [Hg]
    rw [show s - 48 + 48 = s by simp]
    repeat mstep
    mcredits R
    iframe Hc
    isplitr
    · ipureintro; trivial
    have hcn : c ≠ 0 := by intro h; subst h; simp at hc8
    ihave HA := heapS_pos hcn $$ HA
    icases HA with ⟨%⟨hp0', hpb⟩, %hl', %hhl, Hinv⟩
    iexists p, hl'
    iframe Hg Hvt Hp Hcap Ho
    isplitr
    · ipureintro; exact hhl
    isplitr [Hb Hinv]
    · iapply join631 n (s.toNat - 96)
      ihave Lo := stk_addr (show (s - 48).toNat - 48 = s.toNat - 96 by omega) $$ Lo
      iframe Lo
      ihave U0 := stk_addr (show s.toNat - 96 + 32 + 16 = s.toNat - 96 + 48 by omega) $$ U0
      iframe U0
      ihave L0 := BorshFT.stkW (b := s.toNat - 96 + 56) c (by omega) $$ L0
      ihave L4 := BorshFT.stkW (b := s.toNat - 96 + 60) 1 (by omega) $$ L4
      ihave O0 := BorshFT.stkW (b := s.toNat - 96 + 64) 0 (by omega) $$ O0
      ihave O4 := BorshFT.stkW (b := s.toNat - 96 + 68) p (by omega) $$ O4
      ihave O8 := BorshFT.stkW (b := s.toNat - 96 + 72) c (by omega) $$ O8
      ihave U1 := stk_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 = s.toNat - 96 + 76 by omega) $$ U1
      ihave C0 := BorshFT.stkW (b := s.toNat - 96 + 80) 0 (by omega) $$ C0
      ihave C4 := BorshFT.stkB (b := s.toNat - 96 + 84) (k := 4) c4 (by omega) hc4 $$ C4
      ihave C8 := BorshFT.stkB (b := s.toNat - 96 + 88) (k := 4) c8 (by omega) hc8' $$ C8
      ihave U2 := stk_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 + 4 + 4 = s.toNat - 96 + 92 by omega) $$ U2
      iframe L0 L4 O0 O4 O8 U1 C0 C4 C8 U2
    iunfold sbuf
    isplitr
    · ipureintro; exact ⟨by simp, hp0', hpb, fun h => absurd h hcn⟩
    isplitl []
    · iapply memBytes_nil
    iunfold block at Hb
    icases Hb with ⟨%jb, %hjb, Hb⟩
    isplitl [Hb]
    · iexists jb
      iframe Hb
      ipureintro; simp; omega
    ihave Hinv := heapInv_mono n maxP hl' _ (max F 1) (F + 2) (by omega) $$ Hinv
    rw [if_neg hcn]
    iexact Hinv
  · -- a later growth: the realloc
    have hcap : 0 < cap.toNat := by
      rcases Nat.eq_zero_or_pos cap.toNat with h | h
      · exact absurd (UInt32.toNat_inj.mp (by simpa using h)) hc0
      · exact h
    ihave Hinv := heapInv_neg hc0 $$ Hinv
    icases Hj with ⟨%junk, %hjunk, Hj⟩
    ihave Hbs := BorshFT.joinB bs junk rfl $$ [Hbs Hj]
    · iframe Hbs Hj
    have key := f627_realloc (GF := GF) cfg lim (d + 1) types[39]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 16) c (s - 48 + 32) (s - 48) ptr cap idx maxP hl ((ptr.toNat, cap.toNat) :: live) F (bs ++ junk) obo
      (by omega) hobo (by omega) hp0 hcap (by omega) hc28 (by simp; omega) (by simp) hr
    rw [if_neg hc0] at hX
    subst hX
    generalize hK : cost154 cfg F cap c = K at key ⊢
    repeat mstep
    mstep [Hcap]
    repeat mstep
    mstep [C8] with (simp [UInt32.toNat_add]; omega)
    repeat mstep
    mstep [C4]
    repeat mstep
    mstep [Hp]
    mstep [C0]
    repeat mstep
    ihave C4 := memBytes_addr (show (s - 48).toNat + 36 = (s - 48 + 32).toNat + 4 by omega) $$ C4
    mcall key using [Hg Lo Hvt Hinv C0 C4 Hbs Os]
    · iframe Hg Lo Hvt Hinv C0 C4 Hbs Os
      ipureintro; rfl
    clear key
    icases HQ with ⟨%hrs, %p, Hg, Lo, Hvt, C0, C4, O0, O4, O8, HA⟩
    subst hrs
    ihave O4 := memBytes_addr (show (s - 48 + 16).toNat + 4 = (s - 48).toNat + 20 by omega) $$ O4
    ihave O0 := memBytes_addr (show (s - 48 + 16).toNat = (s - 48).toNat + 16 by omega) $$ O0
    mcredits (40 * cfg.regularOpCost + R)
    repeat mstep
    mstep [O8] with (simp [UInt32.toNat_add]; omega)
    repeat mstep
    mstep [O4]
    repeat mstep
    mstep [O0]
    repeat mstep
    mstep [Hcap]
    repeat mstep
    mstep [Hp]
    repeat mstep
    mstep [Ho]
    repeat mstep
    mstep [Hg]
    rw [show s - 48 + 48 = s by simp]
    repeat mstep
    mcredits R
    iframe Hc
    isplitr
    · ipureintro; trivial
    have hcn : c ≠ 0 := by intro h; subst h; simp at hc8
    iunfold reallocated at HA
    icases HA with ⟨%⟨hp0', hpb⟩, ⟨%hl', %hhl, Hinv⟩, Hb, %junk2, %hj2, Hj2⟩
    iexists p, hl'
    iframe Hg Hvt Hp Hcap Ho
    isplitr
    · ipureintro; exact hhl
    isplitr [Hb Hj2 Hinv]
    · iapply join631 n (s.toNat - 96)
      ihave Lo := stk_addr (show (s - 48).toNat - 48 = s.toNat - 96 by omega) $$ Lo
      iframe Lo
      ihave U0 := stk_addr (show s.toNat - 96 + 32 + 16 = s.toNat - 96 + 48 by omega) $$ U0
      iframe U0
      ihave L0 := BorshFT.stkW (b := s.toNat - 96 + 56) c (by omega) $$ L0
      ihave L4 := BorshFT.stkW (b := s.toNat - 96 + 60) 1 (by omega) $$ L4
      ihave O0 := BorshFT.stkW (b := s.toNat - 96 + 64) 0 (by omega) $$ O0
      ihave O4 := BorshFT.stkW (b := s.toNat - 96 + 68) p (by omega) $$ O4
      ihave O8 := BorshFT.stkW (b := s.toNat - 96 + 72) c (by omega) $$ O8
      ihave U1 := stk_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 = s.toNat - 96 + 76 by omega) $$ U1
      ihave C0 := BorshFT.stkW (b := s.toNat - 96 + 80) ptr (by omega) $$ C0
      ihave C4 := BorshFT.stkW (b := s.toNat - 96 + 84) cap (by omega) $$ C4
      ihave C8 := BorshFT.stkW (b := s.toNat - 96 + 88) 1 (by omega) $$ C8
      ihave U2 := stk_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 + 4 + 4 = s.toNat - 96 + 92 by omega) $$ U2
      iframe L0 L4 O0 O4 O8 U1 C0 C4 C8 U2
    iunfold sbuf
    isplitr
    · ipureintro; exact ⟨by omega, hp0', hpb, fun h => absurd h hcn⟩
    ihave Hb := BorshFT.splitB bs junk rfl $$ Hb
    icases Hb with ⟨Hb, Hj⟩
    iframe Hb
    isplitl [Hj Hj2]
    · iexists junk ++ junk2
      isplitr
      · ipureintro; simp; omega
      iapply BorshFT.joinB (a := p.toNat + bs.length) (b := p.toNat + cap.toNat) junk junk2 (by omega)
      iframe Hj Hj2
    ihave Hinv := heapInv_mono n maxP hl' _ (max F 1 + 1) (F + 2) (by omega) $$ Hinv
    rw [if_neg hcn]
    simp only [List.erase_cons_head]
    iexact Hinv

end L631

/-! ## Reserving room: `try_reserve` (630), `handle_reserve` (628), `reserve` (623, 589) -/

/-- Room for `k` more bytes past `len` in a buffer of capacity `cap`. -/
abbrev fits (cap len k : UInt32) : Prop := k.toNat ≤ cap.toNat - len.toNat

/-- The capacity after reserving `k` more bytes past `len`. -/
def capAfter (cap len k : UInt32) : UInt32 := if fits cap len k then cap else growCap cap (len + k)

/-- The free list's bound after the reserve. -/
def fAfter (F : Nat) (cap len k : UInt32) : Nat := if fits cap len k then F else F + 2

/-- The memory's length after the reserve. -/
def hlAfter (hl hl' : Nat) (cap len k : UInt32) : Prop :=
  if fits cap len k then hl' = hl else hl' = hl ∨ hl' = grownLen hl (growCap cap (len + k))

/-- The reserve's growth cost: none when the bytes fit. -/
def costRes (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) : Nat :=
  if fits cap len k then 0 else costGrow cfg F cap (growCap cap (len + k))

/-- Room under the limit for the reserve's growth. -/
def roomRes (hl maxP : Nat) (cap len k : UInt32) : Prop :=
  ¬ fits cap len k → roomFor hl maxP (growCap cap (len + k))

section LRes

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem sbuf_pure {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {ptr cap : UInt32} {bs : List UInt8} :
    sbuf (GF := GF) n maxP hl live F ptr cap bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ ptr ≠ 0 ∧ ptr.toNat + cap.toNat < 2 ^ 32 ∧ (cap = 0 → ptr = 1)⌝ ∗
        sbuf n maxP hl live F ptr cap bs := by
  iintro H
  iunfold sbuf at H
  icases H with ⟨%h, H⟩
  isplitr
  · ipureintro; exact h
  iunfold sbuf
  iframe H
  ipureintro; exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`try_reserve(out, vec, len, k)`** (630): `Ok` at `out`, the buffer grown (631) when the `k`
bytes do not fit. -/
theorem f630_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (hs : 96 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hlen : len.toNat = bs.length)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : len.toNat + k.toNat < 2 ^ 27) (hr : roomRes hl maxP cap len k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f630 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 40 * cfg.regularOpCost + costRes cfg F cap len k)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat), ⌜hlAfter hl hl' cap len k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap len k ∗
          n ↦[i32][ out.toNat ] 0 ∗ sbuf n maxP hl' live (fAfter F cap len k) p (capAfter cap len k) bs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, #H631, -, -, -, -, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha631 := hm.funcs 631 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hsb, Ho⟩
  subst hargs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl, -⟩, Hsb⟩
  have hsub : (cap - len).toNat = cap.toNat - len.toNat := by
    rw [UInt32.toNat_sub_of_le]; simp [UInt32.le_iff_toNat_le]; omega
  simp only [f630, costRes, capAfter, fAfter, hlAfter]
  by_cases hfit : fits cap len k
  · have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (cap - len) k) = 1 := by
      simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le, hsub]; omega
    simp only [if_pos hfit]
    repeat mstep
    mstep [Hcap]
    repeat mstep
    mstep [Ho]
    mcredits R
    iframe Hc
    isplitr
    · ipureintro; simp [htype]
    iexists ptr, hl
    iframe Hg Hs Hvt Hp Hcap Ho Hsb
    ipureintro; trivial
  · have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (cap - len) k) = 0 := by
      simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le, hsub]; omega
    simp only [if_neg hfit]
    have key := f631_spec (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt s out vec
      len k ptr cap idx maxP hl live F bs ob hs hob hout hvec hlen hcap2 hlk (by omega) (hr hfit)
    generalize hK : costGrow cfg F cap (growCap cap (len + k)) = K at key ⊢
    repeat mstep
    mstep [Hcap]
    repeat mstep
    mcall key using [Hg Hs Hvt Hp Hcap Hsb Ho]
    · iframe Hg Hs Hvt Hp Hcap Hsb Ho
    clear key
    icases HQ with ⟨%hrs, %p, %hl', %hhl, HQ⟩
    subst hrs
    repeat mstep
    mcredits R
    iframe Hc
    isplitr
    · ipureintro; simp [htype]
    iexists p, hl'
    iframe HQ
    ipureintro; exact hhl

set_option maxRecDepth 100000 in
/-- **`handle_reserve(r)`** (628) on `Ok`: returns. -/
theorem f628_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (r : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f628 Cg
        (fun args => iprop(⌜args = [.i32 r]⌝ ∗ n ↦[i32][ r.toNat ] 0))
        (fun _ => 10 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ r.toNat ] 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Hr⟩ Hc
  subst hargs
  simp only [f628]
  repeat mstep
  mstep [Hr]
  repeat mstep
  mcredits R
  iframe Hc Hr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`RawVec::reserve(vec, len, k)`** (623): 630 into a 16-byte frame, then 628. -/
theorem f623_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hlen : len.toNat = bs.length)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : len.toNat + k.toNat < 2 ^ 27) (hr : roomRes hl maxP cap len k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f623 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ sbuf n maxP hl live F ptr cap bs))
        (fun _ => 130 * cfg.regularOpCost + costRes cfg F cap len k)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat), ⌜hlAfter hl hl' cap len k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap len k ∗
          sbuf n maxP hl' live (fAfter F cap len k) p (capAfter cap len k) bs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, #H630, #H628, -, -, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha630 := hm.funcs 630 (by decide)
  have ha628 := hm.funcs 628 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hsb⟩
  subst hargs
  icases stk_split n (s.toNat - 112) 96 16 $$ Hs with ⟨Lo, Fr⟩
  icases stk_split n (s.toNat - 112 + 96) 4 12 $$ Fr with ⟨O, Fr⟩
  iunfold stk at O
  icases O with ⟨%ob, %hob, O⟩
  ihave O := memBytes_addr (show s.toNat - 112 + 96 = (s - 16).toNat by omega) $$ O
  ihave Lo := stk_addr (show s.toNat - 112 = (s - 16).toNat - 96 by omega) $$ Lo
  have key := f630_spec (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16) vec len k ptr cap idx maxP hl live F bs ob (by omega) hob (by omega) hvec hlen hcap2 hlk hr
  generalize hK : costRes cfg F cap len k = K at key ⊢
  simp only [f623]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall key using [Hg Lo Hvt Hp Hcap Hsb O]
  · iframe Hg Lo Hvt Hp Hcap Hsb O
  clear key
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, Hp, Hcap, O, Hsb⟩
  subst hrs
  mcredits (70 * cfg.regularOpCost + R)
  repeat mstep
  mcall (f628_ok cfg lim (d + 1) types[0]! rfl inst mi n hn Cg (s - 16)) using [O]
  · iframe O
  icases HQ with ⟨%hrs, O⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists p, hl'
  iframe Hg Hvt Hp Hcap Hsb
  isplitr
  · ipureintro; exact hhl
  ihave O := BorshFT.stkW (b := s.toNat - 112 + 96) 0 (by omega) $$ O
  ihave Lo := stk_addr (show (s - 16).toNat - 96 = s.toNat - 112 by omega) $$ Lo
  ihave Fr := stk_join n (s.toNat - 112 + 96) 4 12 $$ [O Fr]
  · iframe O Fr
  iapply stk_join n (s.toNat - 112) 96 16
  iframe Lo Fr

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Vec::reserve(vec, k)`** (589): 623 at the vector's length. -/
theorem f589_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + k.toNat < 2 ^ 27)
    (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f589 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs))
        (fun _ => 160 * cfg.regularOpCost + costRes cfg F cap (UInt32.ofNat bs.length) k)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
            (capAfter cap (UInt32.ofNat bs.length) k) bs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, -, -, #H623, -, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha623 := hm.funcs 623 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have key := f623_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s
    vec (UInt32.ofNat bs.length) k ptr cap idx maxP hl live F bs hs (by omega)
    (by simp; omega) hcap2 (by simp; omega) hr
  generalize hK : costRes cfg F cap (UInt32.ofNat bs.length) k = K at key ⊢
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb⟩
  subst hargs
  simp only [f589]
  repeat mstep
  mstep [Hl]
  repeat mstep
  mcall key using [Hg Hs Hvt Hp Hcap Hsb]
  · iframe Hg Hs Hvt Hp Hcap Hsb
  clear key
  icases HQ with ⟨%hrs, %p, %hl', %hhl, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hl
  isplitr
  · ipureintro; simp [htype]
  iexists p, hl'
  iframe HQ
  ipureintro; exact hhl

end LRes

/-! ## Appending: `push` (614), `spec_extend` (588), `extend_from_slice` (613) -/

/-- The cost of a push or an append of `k` bytes onto `len`. -/
def costApp (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) : Nat :=
  260 * cfg.regularOpCost + costRes cfg F cap len k

section LApp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Opening the first junk byte of a buffer with room, to store a byte there. -/
theorem sbuf_push {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {p c : UInt32} {bs : List UInt8}
    (h : bs.length < c.toNat) :
    sbuf (GF := GF) n maxP hl live F p c bs ⊢ ∃ j : UInt8, n ↦[wms][ p.toNat + bs.length ] [j] ∗
      (∀ x : UInt8, n ↦[wms][ p.toNat + bs.length ] [x] -∗ sbuf n maxP hl live F p c (bs ++ [x])) := by
  iintro H
  iunfold sbuf at H
  icases H with ⟨%⟨hbl, hp0, hpc, hp1⟩, Hb, ⟨%junk, %hj, Hj⟩, Hinv⟩
  obtain ⟨j, js, rfl⟩ : ∃ j js, junk = j :: js := by
    cases junk with
    | nil => simp at hj; omega
    | cons j js => exact ⟨j, js, rfl⟩
  ihave Hj := AllocNewCell.memBytes_eq (show j :: js = [j] ++ js from rfl) $$ Hj
  ihave Hj := BorshFT.splitB [j] js rfl $$ Hj
  icases Hj with ⟨Hj, Hjs⟩
  iexists j
  iframe Hj
  iintro %x Hx
  iunfold sbuf
  isplitr
  · ipureintro; refine ⟨by simp; omega, hp0, hpc, hp1⟩
  ihave Hb := BorshFT.joinB bs [x] rfl $$ [Hb Hx]
  · iframe Hb Hx
  iframe Hb Hinv
  iexists js
  isplitr
  · ipureintro; simp at hj ⊢; omega
  ihave Hjs := memBytes_addr (show p.toNat + bs.length + [j].length = p.toNat + (bs ++ [x]).length by simp; omega) $$ Hjs
  iexact Hjs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Vec::push(vec, b)`** (614): the byte `byteOf b` appended, the buffer grown (589) when full. -/
theorem f614_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec b ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + 1 < 2 ^ 27)
    (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) 1) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f614 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 b]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs))
        (fun _ => costApp cfg F cap (UInt32.ofNat bs.length) 1)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) 1⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) 1 ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + 1) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) 1) p
            (capAfter cap (UInt32.ofNat bs.length) 1) (bs ++ [MemSet.byteOf b]))) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, -, -, -, #H589, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha589 := hm.funcs 589 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb⟩
  subst hargs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl, hp0, hpc, -⟩, Hsb⟩
  simp only [f614, costApp, costRes, capAfter, fAfter, hlAfter]
  by_cases hfit : fits cap (UInt32.ofNat bs.length) 1
  all_goals have hfit' := hfit
  all_goals simp only [fits, hL, UInt32.toNat_one] at hfit'
  · simp only [if_pos hfit]
    have hne : Numeric.bool (Numeric.irelop32 IRelOp.ne (UInt32.ofNat bs.length) cap) = 1 := by
      have : (UInt32.ofNat bs.length) ≠ cap := by
        intro h; have := congrArg UInt32.toNat h; rw [hL] at this; omega
      simp [Numeric.irelop32, Numeric.bool, this]
    repeat mstep
    mstep [Hl]
    mstep; mstep
    mstep [Hcap]
    repeat mstep
    mstep [Hp]
    repeat mstep
    icases sbuf_push (show bs.length < cap.toNat by omega) $$ Hsb with ⟨%j, Hj, Hw⟩
    mstep [Hj] with (simp [UInt32.toNat_add]; omega)
    rw [MemSet.storeBytes_i32_1]
    ispecialize Hw $$ %(MemSet.byteOf b)
    ihave Hsb := Hw $$ Hj
    mstep; mstep; mstep [Hl]
    repeat mstep
    mstep [Hl]
    mcredits R
    iframe Hc
    isplitr
    · ipureintro; simp [htype]
    iexists ptr, hl
    iframe Hg Hs Hvt Hp Hcap Hsb
    isplitr
    · ipureintro; trivial
    have : UInt32.ofNat bs.length + 1 = UInt32.ofNat (bs.length + 1) := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hL]; simp <;> omega
    rw [this]
    iexact Hl
  · simp only [if_neg hfit]
    have heq : UInt32.ofNat bs.length = cap := by
      apply UInt32.toNat_inj.mp; rw [hL]; omega
    have hne : Numeric.bool (Numeric.irelop32 IRelOp.ne (UInt32.ofNat bs.length) cap) = 0 := by
      simp [Numeric.irelop32, Numeric.bool, heq]
    have key := f589_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt s
      vec 1 ptr cap idx maxP hl live F bs hs hvec hcap2 (by simp; omega) hr
    simp only [costRes, capAfter, fAfter, hlAfter, if_neg hfit] at key
    generalize hK : costGrow cfg F cap (growCap cap (UInt32.ofNat bs.length + 1)) = K at key ⊢
    generalize hc : growCap cap (UInt32.ofNat bs.length + 1) = c at key ⊢
    have hgc := growCap_toNat cap (UInt32.ofNat bs.length + 1) (by omega)
    rw [hc] at hgc
    have h1 : (UInt32.ofNat bs.length + 1).toNat = bs.length + 1 := by rw [UInt32.toNat_add, hL]; simp <;> omega
    rw [h1] at hgc
    repeat mstep
    mstep [Hl]
    mstep; mstep
    mstep [Hcap]
    repeat mstep
    mcall key using [Hg Hs Hvt Hp Hcap Hl Hsb]
    · iframe Hg Hs Hvt Hp Hcap Hl Hsb
    clear key
    icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb⟩
    subst hrs
    icases sbuf_pure $$ Hsb with ⟨%⟨hbl', hp0', hpc', -⟩, Hsb⟩
    mcredits (60 * cfg.regularOpCost + R)
    repeat mstep
    mstep [Hl]
    repeat mstep
    mstep [Hp]
    repeat mstep
    icases sbuf_push (show bs.length < c.toNat by
      omega) $$ Hsb with ⟨%j, Hj, Hw⟩
    mstep [Hj] with (simp [UInt32.toNat_add]; omega)
    rw [MemSet.storeBytes_i32_1]
    ispecialize Hw $$ %(MemSet.byteOf b)
    ihave Hsb := Hw $$ Hj
    mstep; mstep; mstep [Hl]
    repeat mstep
    mstep [Hl]
    mcredits R
    iframe Hc
    isplitr
    · ipureintro; simp [htype]
    iexists p, hl'
    iframe Hg Hs Hvt Hp Hcap Hsb
    isplitr
    · ipureintro; exact hhl
    have : UInt32.ofNat bs.length + 1 = UInt32.ofNat (bs.length + 1) := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hL]; simp <;> omega
    rw [this]
    iexact Hl

/-- Opening the first `k` junk bytes of a buffer with room, to copy `k` bytes there. -/
theorem sbuf_app {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {p c : UInt32} {bs : List UInt8}
    (k : Nat) (h : bs.length + k ≤ c.toNat) :
    sbuf (GF := GF) n maxP hl live F p c bs ⊢ ∃ jb : List UInt8, ⌜jb.length = k⌝ ∗
      n ↦[wms][ p.toNat + bs.length ] jb ∗
      (∀ xs : List UInt8, ⌜xs.length = k⌝ -∗ n ↦[wms][ p.toNat + bs.length ] xs -∗
        sbuf n maxP hl live F p c (bs ++ xs)) := by
  iintro H
  iunfold sbuf at H
  icases H with ⟨%⟨hbl, hp0, hpc, hp1⟩, Hb, ⟨%junk, %hj, Hj⟩, Hinv⟩
  ihave Hj := AllocNewCell.memBytes_eq (List.take_append_drop k junk).symm $$ Hj
  ihave Hj := BorshFT.splitB (junk.take k) (junk.drop k) rfl $$ Hj
  icases Hj with ⟨Hj, Hjs⟩
  iexists junk.take k
  isplitr
  · ipureintro; simp; omega
  iframe Hj
  iintro %xs %hxs Hx
  iunfold sbuf
  isplitr
  · ipureintro; refine ⟨by simp; omega, hp0, hpc, hp1⟩
  ihave Hb := BorshFT.joinB bs xs rfl $$ [Hb Hx]
  · iframe Hb Hx
  iframe Hb Hinv
  iexists junk.drop k
  isplitr
  · ipureintro; simp; omega
  ihave Hjs := memBytes_addr (show p.toNat + bs.length + (junk.take k).length = p.toNat + (bs ++ xs).length by
    simp; omega) $$ Hjs
  iexact Hjs

/-- The cost of an append of `k` bytes: the reserve and the copy. -/
def costExt (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) : Nat :=
  costApp cfg F cap len k + MemCpy.cost k.toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`spec_extend(vec, src, src + k)`** (588): the `k` bytes at `src` appended (589, then 951). -/
theorem f588_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec src k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + k.toNat < 2 ^ 27)
    (hsb : sb.length = k.toNat) (hsrc : src.toNat + k.toNat ≤ 2 ^ 32)
    (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f588 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 src, .i32 (src + k)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ src.toNat ] sb))
        (fun _ => costExt cfg F cap (UInt32.ofNat bs.length) k)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + k.toNat) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
            (capAfter cap (UInt32.ofNat bs.length) k) (bs ++ sb) ∗ n ↦[wms][ src.toNat ] sb)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, #HR, -, -, -, -, -, #H589, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -, -, -, -, -, -, #H951, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha589 := hm.funcs 589 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have t15r : types[15]!.results.length = 1 := by rfl
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
  have hsk : src + k - src = k := by rw [UInt32.add_comm]; exact UInt32.add_sub_cancel k src
  have key := f589_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt s
    vec k ptr cap idx maxP hl live F bs hs hvec hcap2 hlk hr
  unfold costExt costApp
  generalize hK : costRes cfg F cap (UInt32.ofNat bs.length) k = K at key ⊢
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  have hM2 : (11 + MemCpy.cost k.toNat) * cfg.regularOpCost = 11 * cfg.regularOpCost + M := by
    rw [Nat.add_mul, hM]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb, Hsrc⟩
  subst hargs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl, -⟩, Hsb⟩
  rw [show 260 * cfg.regularOpCost + K + M + R = 260 * cfg.regularOpCost + K + (M + R) by omega]
  simp only [f588]
  repeat mstep
  rw [hsk]
  mcall key using [Hg Hs Hvt Hp Hcap Hl Hsb]
  · iframe Hg Hs Hvt Hp Hcap Hl Hsb
  clear key
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb⟩
  subst hrs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl', hp0', hpc', -⟩, Hsb⟩
  have hroom : bs.length + k.toNat ≤ (capAfter cap (UInt32.ofNat bs.length) k).toNat := by
    by_cases h : fits cap (UInt32.ofNat bs.length) k
    · simp only [capAfter, if_pos h]; simp only [fits, hL] at h; omega
    · simp only [capAfter, if_neg h]
      rw [growCap_toNat _ _ (by omega)]
      have : (UInt32.ofNat bs.length + k).toNat = bs.length + k.toNat := by
        rw [UInt32.toNat_add, hL]; omega
      rw [this]; omega
  generalize hca : capAfter cap (UInt32.ofNat bs.length) k = ca at hroom hpc' ⊢
  icases sbuf_app k.toNat hroom $$ Hsb with ⟨%jb, %hjb, Hj, Hw⟩
  mcredits (80 * cfg.regularOpCost + (M + R))
  repeat mstep
  mstep [Hp]
  mstep
  mstep [Hl]
  repeat mstep
  ihave Hj := memBytes_addr (show p.toNat + bs.length = (p + UInt32.ofNat bs.length).toNat by
    rw [UInt32.toNat_add, hL]; omega) $$ Hj
  mcall (MemCpy.f951_spec cfg lim (d + 1) types[15]! t15r inst mi n hn Cg (p + UInt32.ofNat bs.length) src k jb sb
      (by omega) hsb (by rw [UInt32.toNat_add, hL]; omega) hsrc) using [Hj Hsrc]
  · iunfold MemCpy.pre
    iframe Hj Hsrc
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Hj, Hsrc⟩
  subst hrs
  try rw [hM2]
  mcredits (40 * cfg.regularOpCost + R)
  repeat mstep
  mstep [Hl]
  repeat mstep
  mstep [Hl]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists p, hl'
  iframe Hg Hs Hvt Hp Hcap Hsrc
  isplitr
  · ipureintro; exact hhl
  have : UInt32.ofNat bs.length + k = UInt32.ofNat (bs.length + k.toNat) := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hL]; simp <;> omega
  rw [this]
  iframe Hl
  ihave Hj := memBytes_addr (show (p + UInt32.ofNat bs.length).toNat = p.toNat + bs.length by
    rw [UInt32.toNat_add, hL]; omega) $$ Hj
  iapply Hw $$ %sb %hsb Hj

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`extend_from_slice(vec, src, k)`** (613): 588 on `src .. src + k`. -/
theorem f613_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec src k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + k.toNat < 2 ^ 27)
    (hsb : sb.length = k.toNat) (hsrc : src.toNat + k.toNat ≤ 2 ^ 32)
    (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f613 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 src, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ src.toNat ] sb))
        (fun _ => 20 * cfg.regularOpCost + costExt cfg F cap (UInt32.ofNat bs.length) k)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + k.toNat) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
            (capAfter cap (UInt32.ofNat bs.length) k) (bs ++ sb) ∗ n ↦[wms][ src.toNat ] sb)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, -, -, -, -, #H588, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha588 := hm.funcs 588 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have key := f588_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s
    vec src k ptr cap idx maxP hl live F bs sb hs hvec hcap2 hlk hsb hsrc hr
  generalize hK : costExt cfg F cap (UInt32.ofNat bs.length) k = K at key ⊢
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f613]
  repeat mstep
  mcall key using [HP]
  · iframe HP
  clear key
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexact HQ

end LApp

end WNear.Binary.ScratchGrow
