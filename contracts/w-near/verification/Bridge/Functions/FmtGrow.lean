import Bridge.Functions.VecWithCap
import Binary.Code.Part13
import Binary.Code.Part14
import NearLogic.Tactic.Control

/-!
# Growing an empty `String` (M5): `finish_grow` (772) and `grow_amortized` (776)

`String`'s `write_str` (759 → 757 → 734) reserves room with `RawVec::reserve` (735 → 768 →
775). When the `String` is empty (capacity 0) and `k > 0` bytes are written, `reserve` calls
`grow_amortized` (776):

```
776 grow_amortized(out, vec, len, k)   frame 48: new_cap = max(2·cap, len + k, 8);
                                       Layout::array::<u8>(new_cap) (752) at sp+8;
                                       current_memory: cap = 0 ⇒ None (word 0 at sp+32);
                                       finish_grow(sp+16, new_cap, 1, sp+32, sp) (772);
                                       Ok(ptr) ⇒ vec.ptr = ptr, vec.cap = new_cap; out = 0 (Ok)
772 finish_grow(out, size, 1, cur, _)  frame 16: cur = None ⇒ Global::allocate(size) (769)
                                       at sp; ptr ≠ 0 ⇒ out = (0, ptr, size) (Ok)
```

Both are specified on that path: capacity 0, a nonzero size below `2^28` with room for the
allocation (`roomFor`, so the allocation succeeds: `heapAfter_ne`).
-/

namespace WNear.Binary.FmtGrow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word roomFor heapAfter costAlloc pre68x post68x
  heapAfter_ne stk_addr)
open WNear.Binary.VecWithCap (okG costAllocF vecCode2 f769_spec f752_spec pre752 post752)

/-! ## `finish_grow` (772) -/

section L772

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre772 (n g : Nat) (gt : GlobalType) (s out size cur x : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 size, .i32 1, .i32 cur, .i32 x]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[i32][ cur.toNat ] 0 ∗ n ↦[wms][ out.toNat ] ob)

def post772 (n g : Nat) (gt : GlobalType) (s out size cur : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗
    vt n 1057464 idx ta a578 ∗ n ↦[i32][ cur.toNat ] 0 ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] size ∗
    heapAfter n maxP len live F false size p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `finish_grow(out, size, 1, None)` (772): `Global::allocate(size)` (769), `Ok((ptr, size))`
at `out`. -/
theorem f772_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size cur x : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hs : 48 ≤ s.toNat)
    (hsize1 : 0 < size.toNat) (hsize2 : size.toNat < 2 ^ 28) (hr : roomFor len maxP size)
    (F : Nat := 1) (hF : okG F := by decide) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f772 Cg
        (pre772 n g gt s out size cur x idx ta (A 578) maxP len live F ob)
        (fun _ => 123 * cfg.regularOpCost + costAllocF cfg F size)
        (post772 n g gt s out size cur idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H769 : A 769 ↪[wf] FuncInst.wasm types[31]! inst f769 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha769 := hm.funcs 769 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 8 := by simp; omega
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_s size 0) = 1 := by
    have h' : size.toNat < 2147483648 := by omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre772 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hcur, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  ihave Ho4 := U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by omega) $$ Ho4
  icases Ho4 with ⟨Ho4, Ho8⟩
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs with ⟨X, Hs⟩
  icases stk_split n (s.toNat - 48 + 32) 8 8 $$ Hs with ⟨Z, Y⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  simp only [f772]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcur]
  repeat mstep
  mcall (f769_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16) size idx maxP len live zb hzb (by omega) hsize2 (fun _ => hr) (F := F) (hF := hF)) using [Hg X Hvt Hinv Z]
  · iunfold pre68x
    ihave X := stk_addr (show s.toNat - 48 = (s - 16).toNat - 32 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 48 + 32 = (s - 16).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; rfl
  iunfold post68x at HQ
  icases HQ with ⟨%hrs, %p, Hg, X, Hvt, Z0, Z4, HA⟩
  subst hrs
  ihave HA := heapAfter_ne $$ HA
  icases HA with ⟨%hp0, HA⟩
  repeat mstep
  mstep [Z4]
  repeat mstep
  mstep [Z0]
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
  iunfold post772
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Hcur Ho0 Ho4 Ho8 HA
  ihave X := stk_addr (show (s - 16).toNat - 32 = s.toNat - 48 by omega) $$ X
  ihave Z0 := stk_word n _ p $$ Z0
  ihave Z4 := stk_word n _ size $$ Z4
  ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
  · iframe Z0 Z4
  ihave Z := stk_addr (show (s - 16).toNat = s.toNat - 48 + 32 by omega) $$ Z
  ihave Z := stk_join n (s.toNat - 48 + 32) 8 8 $$ [Z Y]
  · iframe Z Y
  iapply stk_join n (s.toNat - 48) 32 16
  iframe X Z

end L772

/-! ## `select` -/

section Sel

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

/-- `select` in `mstep`'s flexible form: `a` if the condition is nonzero, else `b`. -/
theorem mwpi_select' {t : Option (List ValType)} {rest : List Value} {a b : Value} {c : UInt32} :
    credits Cg K ∗ ⌜vs.reverse = .i32 c :: b :: a :: rest ∧ cfg.regularOpCost ≤ K ∧ True⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal (rest.reverse ++ [if c = 0 then b else a]) f)
      ⊢ mwpi cfg lim d f vs [.select t] Φ :=
  credits_flex fun hs _ => by
    have e : vs = rest.reverse ++ [a, b, .i32 c] := by
      rw [← List.reverse_reverse vs, hs]; simp
    rw [e]
    by_cases h : c = 0
    · subst h; simp only [ite_true]; exact mwpi_select_false t a b
    · simp only [h, ite_false]; exact mwpi_select_true t a b c h

end Sel

set_option hygiene false in
/-- Step a `select` (`mwpi_select'`), then normalise as `mstep` does. -/
macro "msel" : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post))

/-! ## `grow_amortized` (776) -/

section L776

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The new capacity of an empty `RawVec<u8>` asked for `len + k` bytes: `max (len + k) 8`. -/
def newCap (len k : UInt32) : UInt32 := if 8 < len.toNat + k.toNat then len + k else 8

def pre776 (n g : Nat) (gt : GlobalType) (s out vec len k p0 : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗
    n ↦[i32][ vec.toNat ] p0 ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗ n ↦[wms][ out.toNat ] ob)

def post776 (n g : Nat) (gt : GlobalType) (s out vec len k : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 96) 96 ∗
    vt n 1057464 idx ta a578 ∗ n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] newCap len k ∗
    n ↦[i32][ out.toNat ] 0 ∗ heapAfter n maxP hl live F false (newCap len k) p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `grow_amortized(out, vec, len, k)` (776) on an empty `RawVec<u8>`: the capacity
`max (len + k) 8` allocated (772), `Ok` at `out`. -/
theorem f776_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec len k p0 : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 4) (hs : 96 ≤ s.toNat)
    (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hout : out.toNat + 4 ≤ 2 ^ 32) (hk : len.toNat + k.toNat < 2 ^ 28)
    (hr : roomFor hl maxP (newCap len k)) (F : Nat := 1) (hF : okG F := by decide) :
    vecCode2 n maxP inst mi A ∗ A 772 ↪[wf] FuncInst.wasm types[39]! inst f772
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f776 Cg
        (pre776 n g gt s out vec len k p0 idx ta (A 578) maxP hl live F ob)
        (fun _ => 301 * cfg.regularOpCost + costAllocF cfg F (newCap len k))
        (post776 n g gt s out vec len k idx ta (A 578) maxP hl live F) := by
  iintro ⟨#Hv, #H772⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H752 : A 752 ↪[wf] FuncInst.wasm types[14]! inst f752 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H751 : A 751 ↪[wf] FuncInst.wasm types[14]! inst f751 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha752 := hm.funcs 752 (by decide)
  have ha772 := hm.funcs 772 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t39 : types[39]!.params.length = 5 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlk : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (len + k) len) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre776 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp0, Hcap, Ho⟩
  subst hargs
  simp only [f776]
  have hsh : (UInt32.ofNat 0 <<< (1 % 32)) = 0 := by decide
  have hgt0 : Numeric.bool (Numeric.irelop32 IRelOp.gt_u 0 (len + k)) = 0 := by
    simp [Numeric.irelop32, Numeric.bool]
  have hnc : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + k) 8) = 0 then Value.i32 8
      else Value.i32 (len + k)) = Value.i32 (newCap len k) := by
    unfold newCap
    by_cases h8 : 8 < len.toNat + k.toNat
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + k) 8) = 1 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk]; omega
      simp [this, h8]
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + k) 8) = 0 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk]; omega
      simp [this, h8]
  have hnc1 : 0 < (newCap len k).toNat := by
    unfold newCap; split <;> simp_all <;> omega
  have hnc2 : (newCap len k).toNat < 2 ^ 28 := by
    unfold newCap; split <;> simp_all <;> omega
  icases stk_split n (s.toNat - 96) 32 64 $$ Hs with ⟨A1, Hs⟩
  icases stk_split n (s.toNat - 96 + 32) 16 48 $$ Hs with ⟨A2, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16) 8 40 $$ Hs with ⟨U0, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8) 8 32 $$ Hs with ⟨Lay, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8) 12 20 $$ Hs with ⟨O7, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12) 4 16 $$ Hs with ⟨U28, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4) 4 12 $$ Hs with ⟨Cur, U36⟩
  iunfold stk at Lay O7 Cur
  icases Lay with ⟨%lb, %hlb, Lay⟩
  icases O7 with ⟨%ob7, %hob7, O7⟩
  icases Cur with ⟨%cb, %hcb, Cur⟩
  ihave Lay := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 = (s - 48 + 8).toNat by
    simp [UInt32.toNat_add, h48]; omega) $$ Lay
  ihave Cur := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 = (s - 48).toNat + 32 by
    omega) $$ Cur
  ihave O7 := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 = (s - 48 + 16).toNat by
    simp [UInt32.toNat_add, h48]; omega) $$ O7
  try simp only [f776]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  msel
  repeat mstep
  msel
  simp only [hsh, hgt0, ite_true, hnc]
  mcall (f752_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 8) (newCap len k) lb hlb (by omega)) using [Hg A2 Lay]
  · iunfold pre752
    ihave A2 := stk_addr (show s.toNat - 96 + 32 = (s - 48).toNat - 16 by omega) $$ A2
    iframe Hg A2 Lay
    ipureintro; rfl
  iunfold post752 at HQ
  icases HQ with ⟨%hrs, Hg, A2, L0, L4⟩
  subst hrs
  repeat mstep
  mstep [L4]
  repeat mstep
  mstep [L0]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Cur]
  repeat mstep
  mcall (f772_spec cfg lim (d + 1) types[39]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 16) (newCap len k) (s - 48 + 32) (s - 48) idx maxP hl live ob7 hob7
      (by simp [UInt32.toNat_add, h48]; omega) (by omega) hnc1 hnc2 hr (F := F) (hF := hF)) using [Hg A1 A2 Hvt Hinv Cur O7]
  · iunfold pre772
    ihave A2 := stk_addr (show (s - 48).toNat - 16 = s.toNat - 96 + 32 by omega) $$ A2
    ihave A1 := stk_join n (s.toNat - 96) 32 16 $$ [A1 A2]
    · iframe A1 A2
    ihave A1 := stk_addr (show s.toNat - 96 = (s - 48).toNat - 48 by omega) $$ A1
    ihave Cur := memBytes_addr (show (s - 48).toNat + 32 = (s - 48 + 32).toNat by
      simp [UInt32.toNat_add, h48]; omega) $$ Cur
    iframe Hg A1 Hvt Hinv Cur O7
    ipureintro; rfl
  iunfold post772 at HQ
  icases HQ with ⟨%hrs, %p, Hg, A1, Hvt, Cur, Q0, Q4, Q8, HA⟩
  subst hrs
  repeat mstep
  mstep [Q8]
  repeat mstep
  mstep [Q4]
  repeat mstep
  mstep [Q0]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hp0]
  repeat mstep
  mstep [Ho]
  repeat mstep
  mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  iunfold post776
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Hp0 Hcap Ho HA
  -- the stack back
  ihave A1 := stk_addr (show (s - 48).toNat - 48 = s.toNat - 96 by omega) $$ A1
  ihave Q0 := stk_word n _ 0 $$ Q0
  ihave Q4 := stk_word n _ p $$ Q4
  ihave Q8 := stk_word n _ (newCap len k) $$ Q8
  ihave Q := stk_join n _ 4 4 $$ [Q0 Q4]
  · iframe Q0 Q4
  ihave Q := stk_join n _ 8 4 $$ [Q Q8]
  · iframe Q; iapply stk_addr (show (s - 48 + 16).toNat + 8 = (s - 48 + 16).toNat + 4 + 4 by omega) $$ Q8
  ihave L0 := stk_word n _ (newCap len k) $$ L0
  ihave L4 := stk_word n _ 1 $$ L4
  ihave L := stk_join n _ 4 4 $$ [L0 L4]
  · iframe L0 L4
  ihave Cur := stk_word n _ 0 $$ Cur
  ihave L := stk_addr (show (s - 48 + 8).toNat = s.toNat - 96 + 32 + 16 + 8 by
    simp [UInt32.toNat_add, h48]; omega) $$ L
  ihave Q := stk_addr (show (s - 48 + 16).toNat = s.toNat - 96 + 32 + 16 + 8 + 8 by
    simp [UInt32.toNat_add, h48]; omega) $$ Q
  ihave Cur := stk_addr (show (s - 48 + 32).toNat = s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 by
    simp [UInt32.toNat_add, h48]; omega) $$ Cur
  ihave X := stk_join n _ 4 12 $$ [Cur U36]
  · iframe Cur U36
  ihave X := stk_join n _ 4 16 $$ [U28 X]
  · iframe U28 X
  ihave X := stk_join n _ 12 20 $$ [Q X]
  · iframe Q X
  ihave X := stk_join n _ 8 32 $$ [L X]
  · iframe L X
  ihave X := stk_join n _ 8 40 $$ [U0 X]
  · iframe U0 X
  ihave X := stk_addr (show s.toNat - 96 + 32 + 16 = s.toNat - 96 + 48 by omega) $$ X
  iapply stk_join n (s.toNat - 96) 48 48
  iframe A1 X

end L776

end WNear.Binary.FmtGrow
