import Bridge.Functions.VecGrow
import Bridge.Functions.FmtSink

/-!
# Growing a nonempty `String` of `fmt::write`'s sink (759): `finish_grow` (772) and
`grow_amortized` (776) through `__rust_realloc`

`FmtGrow` specifies 772 and 776 on an empty `String`. When the `String` already holds a block
`(ptr, cap)`, `cap ≠ 0`, `grow_amortized` passes the current memory `Some(ptr, cap, align 1)` at
`sp + 32` and `finish_grow` reallocates (`VecGrow.f312_spec`):

```
776 grow_amortized(out, vec, len, k)   frame 48: c := max(2·cap, len + k, 8) (= VecGrow.growCap);
                                       Layout::array::<u8>(c) (752) at sp + 8;
                                       cap ≠ 0 ⇒ [sp+32..44] := (ptr, cap, 1);
                                       finish_grow(sp + 16, c, 1, sp + 32, sp) (772);
                                       Ok(p, c) ⇒ vec.ptr := p, vec.cap := c; out := 0 (Ok)
772 finish_grow(out, c, 1, cur, _)     frame 16: cur = Some(ptr, cap), cap ≠ 0 ⇒
                                       p := __rust_realloc(ptr, cap, 1, c) (312); p ≠ 0 ⇒ out := (0, p, c)
```

772's code is 714's (`VecGrow.f714_spec`) but for the allocation calls of the other branches, so
`f772_re` is `f714_spec`'s proof. 776's frame and stack are `FmtGrow.f776_spec`'s (96 bytes), the
capacity `VecGrow.f716_spec`'s.
-/

namespace WNear.Binary.FmtGrowRe

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (vecCode2 f752_spec pre752 post752)
open WNear.Binary.FmtGrow (mwpi_select')
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.VecGrow (reallocCode reallocated preR postR pre154 post154 cost154 f312_spec growCap
  growCap_toNat pre714 post714)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`finish_grow(out, c, 1, cur, _)`** (772) with the current memory `Some(ptr, cap)`, `cap ≠ 0`:
`__rust_realloc(ptr, cap, 1, c)` (312), `Ok((p, c))` at `out`. -/
theorem f772_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c cur x ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (bs ob : List UInt8) (hs : 32 ≤ s.toNat) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hcur : cur.toNat + 8 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcc : cap.toNat < c.toNat)
    (hc : c.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat) (hlive : (ptr.toNat, cap.toNat) ∈ live)
    (hr : roomFor hl maxP c) :
    reallocCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f772 Cg
        (pre714 n g gt s out c cur x ptr cap idx ta (A 578) maxP hl live F bs ob)
        (fun _ => 140 * cfg.regularOpCost + cost154 cfg F cap c)
        (post714 n g gt s out c cur ptr cap idx ta (A 578) maxP hl live F bs) := by
  iintro #HR
  ihave #S312 := f312_spec (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    ptr cap c idx maxP hl live F bs (by rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega)
    hcap hcc hc hbs hlive hr $$ HR
  iunfold reallocCode at HR
  icases HR with ⟨#H, -, -, -, -, #H312⟩
  iunfold code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha312 := hm.funcs 312 (by decide)
  have t33 : types[33]!.params.length = 4 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_s c 0) = 1 := by
    have h' : c.toNat < 2147483648 := by omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  have hcap0 : cap ≠ 0 := by intro h; subst h; simp at hcap
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : ((ob.drop 4).take 4).length = 4 := by simp; omega
  have hob8 : ((ob.drop 4).drop 4).length = 4 := by simp; omega
  generalize hK : cost154 cfg F cap c = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre714 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp, Hcap, Hbs, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  ihave Ho4 := U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho4
  icases Ho4 with ⟨Ho4, Ho8⟩
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Lo, Fr⟩
  simp only [f772]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hp]
  mstep
  mstep_taken with (simp; exact hptr)
  repeat mstep
  mstep [Hcap]
  mstep
  mstep_taken with (simp; exact hcap0)
  repeat mstep
  mcall S312 using [Hg Lo Hvt Hinv Hbs]
  · iunfold preR
    ihave Lo := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv Hbs
  iunfold post154 at HQ
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  iunfold postR at HQ
  icases HQ with ⟨Hg, Lo, Hvt, HA⟩
  iunfold reallocated at HA
  icases HA with ⟨%⟨hp0, hpb⟩, HA⟩
  mcredits (40 * cfg.regularOpCost + R)
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
  iunfold post714
  isplitr
  · ipureintro; rfl
  iexists p
  iframe Hg Hvt Hp Hcap Ho0 Ho4 Ho8
  isplitl [Lo Fr]
  · ihave Lo := stk_addr (show (s - 16).toNat - 16 = s.toNat - 32 by omega) $$ Lo
    iapply stk_join n (s.toNat - 32) 16 16
    iframe Lo Fr
  iunfold reallocated
  iframe HA
  ipureintro; exact ⟨hp0, hpb⟩

/-- 776's precondition on a nonempty buffer: `VecGrow.pre716` with 96 bytes of stack. -/
def pre776r (n g : Nat) (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗
    n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[wms][ ptr.toNat ] bs ∗
    n ↦[wms][ out.toNat ] ob)

def post776r (n g : Nat) (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32)
    (ta a578 maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 96) 96 ∗
    vt n 1057464 idx ta a578 ∗ n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] growCap cap (len + k) ∗
    n ↦[i32][ out.toNat ] 0 ∗ reallocated n maxP hl live F ptr cap (growCap cap (len + k)) p bs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`grow_amortized(out, vec, len, k)`** (776) on a nonempty buffer `(ptr, cap)`: the capacity
`growCap cap (len + k)` reallocated (772), `Ok` at `out`. -/
theorem f776_re (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (hs : 96 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : len.toNat + k.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (len + k))) :
    vecCode2 n maxP inst mi A ∗ reallocCode n maxP inst mi A ∗ A 772 ↪[wf] FuncInst.wasm types[39]! inst f772
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f776 Cg
        (pre776r n g gt s out vec len k ptr cap idx ta (A 578) maxP hl live F bs ob)
        (fun _ => 400 * cfg.regularOpCost + cost154 cfg F cap (growCap cap (len + k)))
        (post776r n g gt s out vec len k ptr cap idx ta (A 578) maxP hl live F bs) := by
  have hlk' : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
  have hgc := growCap_toNat cap (len + k) (by omega)
  iintro ⟨#Hv, #HR, #H772⟩
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
  have hcap0 : cap ≠ 0 := by intro h; subst h; simp at hcap
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
  have hnc1 : 0 < (growCap cap (len + k)).toNat := by rw [hgc]; omega
  have hnc2 : (growCap cap (len + k)).toNat < 2 ^ 28 := by rw [hgc]; omega
  have hcc : cap.toNat < (growCap cap (len + k)).toNat := by rw [hgc]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre776r at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp, Hcap, Hbs, Ho⟩
  subst hargs
  icases stk_split n (s.toNat - 96) 32 64 $$ Hs with ⟨A1, Hs⟩
  icases stk_split n (s.toNat - 96 + 32) 16 48 $$ Hs with ⟨A2, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16) 8 40 $$ Hs with ⟨U0, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8) 8 32 $$ Hs with ⟨Lay, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8) 12 20 $$ Hs with ⟨O7, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12) 4 16 $$ Hs with ⟨U28, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4) 4 12 $$ Hs with ⟨Cur, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4) 4 8 $$ Hs with ⟨Cur4, Hs⟩
  icases stk_split n (s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 + 4) 4 4 $$ Hs with ⟨Cur8, U44⟩
  iunfold stk at Lay O7 Cur Cur4 Cur8
  icases Lay with ⟨%lb, %hlb, Lay⟩
  icases O7 with ⟨%ob7, %hob7, O7⟩
  icases Cur with ⟨%cb, %hcb, Cur⟩
  icases Cur4 with ⟨%cb4, %hcb4, Cur4⟩
  icases Cur8 with ⟨%cb8, %hcb8, Cur8⟩
  ihave Lay := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 = (s - 48 + 8).toNat by
    simp [UInt32.toNat_add, h48]; omega) $$ Lay
  ihave Cur := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 = (s - 48).toNat + 32 by
    omega) $$ Cur
  ihave Cur4 := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 = (s - 48).toNat + 36 by
    omega) $$ Cur4
  ihave Cur8 := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 + 4 = (s - 48 + 32 + 8).toNat by
    simp [UInt32.toNat_add, h48]; omega) $$ Cur8
  ihave O7 := memBytes_addr (show s.toNat - 96 + 32 + 16 + 8 + 8 = (s - 48 + 16).toNat by
    simp [UInt32.toNat_add, h48]; omega) $$ O7
  simp only [f776]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  msel
  simp only [hsel1]
  repeat mstep
  msel
  simp only [hsel2]
  mcall (f752_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 8) (growCap cap (len + k)) lb hlb (by omega)) using [Hg A2 Lay]
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
  mstep [Cur8]
  repeat mstep
  mstep [Cur4]
  repeat mstep
  mstep [Hp]
  mstep [Cur]
  repeat mstep
  ihave A1 := stk_addr (show s.toNat - 96 = (s - 48).toNat - 32 - 16 by omega) $$ A1
  icases stk_split n _ 16 16 $$ A1 with ⟨A1a, A1b⟩
  ihave A1b := stk_addr (show (s - 48).toNat - 32 - 16 + 16 = (s - 48).toNat - 32 by omega) $$ A1b
  ihave A1b := stk_join n ((s - 48).toNat - 32) 16 16 $$ [A1b A2]
  · iframe A1b
    iapply stk_addr _ $$ A2; omega
  mcall (f772_re cfg lim (d + 1) types[39]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
      (s - 48 + 16) (growCap cap (len + k)) (s - 48 + 32) (s - 48) ptr cap idx maxP hl live F bs ob7
      (by omega) hob7 (by simp [UInt32.toNat_add, h48]; omega) (by simp [UInt32.toNat_add, h48]; omega)
      hptr hcap hcc hnc2 hbs hlive hr) using [Hg A1b Hvt Hinv Cur Cur4 Hbs O7]
  · iunfold pre714
    ihave Cur := memBytes_addr (show (s - 48).toNat + 32 = (s - 48 + 32).toNat by
      simp [UInt32.toNat_add, h48]; omega) $$ Cur
    ihave Cur4 := memBytes_addr (show (s - 48).toNat + 36 = (s - 48 + 32).toNat + 4 by
      simp [UInt32.toNat_add, h48]; omega) $$ Cur4
    iframe Hg A1b Hvt Hinv Cur Cur4 Hbs O7
    ipureintro; rfl
  iunfold post714 at HQ
  icases HQ with ⟨%hrs, %p, Hg, A1b, Hvt, Cur, Cur4, Q0, Q4, Q8, HA⟩
  subst hrs
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
  rw [show s - 48 + 48 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  iunfold post776r
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Hp Hcap Ho HA
  -- the stack back
  ihave Q0 := stk_word n _ 0 $$ Q0
  ihave Q4 := stk_word n _ p $$ Q4
  ihave Q8 := stk_word n _ (growCap cap (len + k)) $$ Q8
  ihave Q := stk_join n _ 4 4 $$ [Q0 Q4]
  · iframe Q0 Q4
  ihave Q := stk_join n _ 8 4 $$ [Q Q8]
  · iframe Q; iapply stk_addr (show (s - 48 + 16).toNat + 8 = (s - 48 + 16).toNat + 4 + 4 by omega) $$ Q8
  ihave L0 := stk_word n _ (growCap cap (len + k)) $$ L0
  ihave L4 := stk_word n _ 1 $$ L4
  ihave L := stk_join n _ 4 4 $$ [L0 L4]
  · iframe L0 L4
  ihave Cur := stk_word n _ ptr $$ Cur
  ihave Cur4 := stk_word n _ cap $$ Cur4
  ihave Cur8 := stk_word n _ 1 $$ Cur8
  ihave L := stk_addr (show (s - 48 + 8).toNat = s.toNat - 96 + 32 + 16 + 8 by
    simp [UInt32.toNat_add, h48]; omega) $$ L
  ihave Q := stk_addr (show (s - 48 + 16).toNat = s.toNat - 96 + 32 + 16 + 8 + 8 by
    simp [UInt32.toNat_add, h48]; omega) $$ Q
  ihave Cur := stk_addr (show (s - 48 + 32).toNat = s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 by
    simp [UInt32.toNat_add, h48]; omega) $$ Cur
  ihave Cur4 := stk_addr (show (s - 48 + 32).toNat + 4 = s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 by
    simp [UInt32.toNat_add, h48]; omega) $$ Cur4
  ihave Cur8 := stk_addr (show (s - 48 + 32 + 8).toNat = s.toNat - 96 + 32 + 16 + 8 + 8 + 12 + 4 + 4 + 4 by
    simp [UInt32.toNat_add, h48]; omega) $$ Cur8
  ihave X := stk_join n _ 4 4 $$ [Cur8 U44]
  · iframe Cur8 U44
  ihave X := stk_join n _ 4 8 $$ [Cur4 X]
  · iframe Cur4 X
  ihave X := stk_join n _ 4 12 $$ [Cur X]
  · iframe Cur X
  ihave X := stk_join n _ 4 16 $$ [U28 X]
  · iframe U28 X
  ihave X := stk_join n _ 12 20 $$ [Q X]
  · iframe Q X
  ihave X := stk_join n _ 8 32 $$ [L X]
  · iframe L X
  ihave X := stk_join n _ 8 40 $$ [U0 X]
  · iframe U0 X
  ihave A1b := stk_addr (show (s - 48).toNat - 32 = s.toNat - 96 + 16 by omega) $$ A1b
  ihave A1 := stk_join n (s.toNat - 96) 16 32 $$ [A1a A1b]
  · isplitl [A1a]
    · iapply stk_addr _ $$ A1a; omega
    iexact A1b
  ihave X := stk_addr (show s.toNat - 96 + 32 + 16 = s.toNat - 96 + 48 by omega) $$ X
  iapply stk_join n (s.toNat - 96) 48 48
  iframe A1 X

end Spec

end WNear.Binary.FmtGrowRe
