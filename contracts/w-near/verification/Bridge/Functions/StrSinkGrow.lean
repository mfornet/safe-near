import Bridge.Functions.StrSink

/-!
# The grow path of `format!`'s `String` sink: 841 and 840 through `finish_grow` (845) (M8)

`spec_extend(v, p, p + k)` (841) without room (`cap - len < k`):

```
841  sp -= 32; c := max(2·cap, len + k, 8); cap ≠ 0 ⇒ Some(ptr, cap, 1) at sp + 16;
     finish_grow(sp, c, 1, sp + 16) (845); Ok(q, c) at sp ⇒ v.ptr := q, v.cap := c;
     memcpy(q + len, p, k) (951); len += k; sp += 32
```

`f841_grow` mirrors `VecGrow.f716_spec` and `VecGrow.f697_grow` in one function, on `gPre`/`gPost`
(the shapes of `VecGrow.growPre`/`growPost` with 48 bytes of stack: 841's frame and 16 bytes for
the realloc). `f840_grow`: `write_str` (840) on top.
-/

namespace WNear.Binary.StrSinkGrow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtSink (add_sub_left)
open WNear.Binary.VecGrow (reallocCode reallocated cost154 growCap growCap_toNat grownV)
open WNear.Binary.StrGrow (pre845 post845 f845_spec)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the `String` sink (persistent): the realloc, 845, 841, 840 and 951. -/
def strCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(reallocCode n maxP inst mi A ∗ A 845 ↪[wf] FuncInst.wasm types[45]! inst f845 ∗
    A 841 ↪[wf] FuncInst.wasm types[31]! inst f841)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (strCode (GF := GF) n maxP inst mi A) := by
  unfold strCode; infer_instance

/-- The `String` `(ptr, cap, |w|)` at `v` holding `w` then `rest`, live; the `k` bytes `sb` at `p`;
48 bytes of stack. -/
def gPre (n g : Nat) (gt : GlobalType) (s v ptr cap p : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w rest sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta a578 ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ v.toNat ] ptr ∗ n ↦[i32][ v.toNat + 4 ] cap ∗
    n ↦[i32][ v.toNat + 8 ] UInt32.ofNat w.length ∗ n ↦[wms][ ptr.toNat ] (w ++ rest) ∗ n ↦[wms][ p.toNat ] sb)

/-- … after: `sb` appended in the buffer reallocated at `q` with the capacity `c`. -/
def gPost (n g : Nat) (gt : GlobalType) (s v ptr cap c p : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w sb : List UInt8) : IProp GF :=
  iprop(∃ q : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ v.toNat ] q ∗ n ↦[i32][ v.toNat + 4 ] c ∗
    n ↦[i32][ v.toNat + 8 ] UInt32.ofNat (w ++ sb).length ∗ n ↦[wms][ q.toNat ] (w ++ sb) ∗
    (∃ tail : List UInt8, ⌜(w ++ sb).length + tail.length = c.toNat⌝ ∗
      n ↦[wms][ q.toNat + (w ++ sb).length ] tail) ∗
    grownV n maxP hl live F ptr cap c q ∗ n ↦[wms][ p.toNat ] sb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`spec_extend(v, p, p + k)`** (841) without room: `c = growCap cap (len + k)` reallocated
through `finish_grow` (845), then the copy (951). -/
theorem f841_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s v ptr cap p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w rest sb : List UInt8) (hs : 48 ≤ s.toNat)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcap2 : cap.toNat < 2 ^ 27)
    (hwr : w.length + rest.length = cap.toNat) (hsb : sb.length = k.toNat)
    (hgrow : cap.toNat < w.length + k.toNat) (hlk : w.length + k.toNat < 2 ^ 27)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k))) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f841 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 p, .i32 (p + k)]⌝ ∗
          gPre n g gt s v ptr cap p idx ta (A 578) maxP hl live F w rest sb))
        (fun _ => 300 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
          cost154 cfg F cap (growCap cap (UInt32.ofNat w.length + k)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ gPost n g gt s v ptr cap (growCap cap (UInt32.ofNat w.length + k)) p
          idx ta (A 578) maxP hl live F w sb)) := by
  have hwl : (UInt32.ofNat w.length).toNat = w.length := by
    simp only [UInt32.toNat_ofNat']; omega
  have hlk' : (UInt32.ofNat w.length + k).toNat = w.length + k.toNat := by
    rw [UInt32.toNat_add, hwl]; omega
  have hgc := growCap_toNat cap (UInt32.ofNat w.length + k) (by omega)
  rw [hlk'] at hgc
  iintro #Hk
  ihave #Hk' := Hk
  iunfold strCode at Hk'
  icases Hk' with ⟨#HR, #H845, -⟩
  ihave #HR' := HR
  iunfold reallocCode at HR'
  icases HR' with ⟨#H, -, #H951, -⟩
  iunfold AllocTwo.code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha845 := hm.funcs 845 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have hcap0 : cap ≠ 0 := by intro h; subst h; simp at hcap
  have hlt5 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (cap - UInt32.ofNat w.length) k) = 1 := by
    have : (cap - UInt32.ofNat w.length).toNat = cap.toNat - w.length := by
      rw [UInt32.toNat_sub_of_le, hwl]; simp [UInt32.le_iff_toNat_le, hwl]; omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, this]; omega
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat w.length + k) (UInt32.ofNat w.length)) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk', hwl]
  have hsh : (cap <<< (1 % 32)).toNat = 2 * cap.toNat := by
    simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hsel1 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (UInt32.ofNat w.length + k)) = 0
      then Value.i32 (UInt32.ofNat w.length + k) else Value.i32 (cap <<< (1 % 32))) =
      Value.i32 (UInt32.ofNat (max (2 * cap.toNat) (w.length + k.toNat))) := by
    by_cases h2 : w.length + k.toNat < 2 * cap.toNat
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (UInt32.ofNat w.length + k)) = 1 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']; omega
      rw [this]; simp only [show (1 : UInt32) ≠ 0 by decide, ite_false, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hsh, UInt32.toNat_ofNat']; omega
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (UInt32.ofNat w.length + k)) = 0 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']; omega
      rw [this]; simp only [ite_true, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hlk', UInt32.toNat_ofNat']; omega
  have hsel2 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u
      (UInt32.ofNat (max (2 * cap.toNat) (w.length + k.toNat))) 8) = 0
      then Value.i32 8 else Value.i32 (UInt32.ofNat (max (2 * cap.toNat) (w.length + k.toNat)))) =
      Value.i32 (growCap cap (UInt32.ofNat w.length + k)) := by
    have hm' : (UInt32.ofNat (max (2 * cap.toNat) (w.length + k.toNat))).toNat =
        max (2 * cap.toNat) (w.length + k.toNat) := by
      rw [UInt32.toNat_ofNat']; omega
    by_cases h8 : 8 < max (2 * cap.toNat) (w.length + k.toNat)
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u
          (UInt32.ofNat (max (2 * cap.toNat) (w.length + k.toNat))) 8) = 1 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, hm']
        simp; omega
      rw [this]; simp only [show (1 : UInt32) ≠ 0 by decide, ite_false, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hgc, hm']; omega
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u
          (UInt32.ofNat (max (2 * cap.toNat) (w.length + k.toNat))) 8) = 0 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, hm']
        simp; omega
      rw [this]; simp only [ite_true, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hgc]; simp; omega
  generalize hC : growCap cap (UInt32.ofNat w.length + k) = c at hgc hsel2 hr ⊢
  generalize hK : cost154 cfg F cap c = K
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  iunfold gPre at HP
  icases HP with ⟨Hg, Hs, Hvt, Hinv, Hp, Hcap, Hlen, Hbs, Hsb⟩
  icases stk_split n (s.toNat - 48) 16 32 $$ Hs with ⟨Lo, Hs⟩
  icases stk_split n (s.toNat - 48 + 16) 12 20 $$ Hs with ⟨O7, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12) 4 16 $$ Hs with ⟨G1, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12 + 4) 4 12 $$ Hs with ⟨C0, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12 + 4 + 4) 4 8 $$ Hs with ⟨C4, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12 + 4 + 4 + 4) 4 4 $$ Hs with ⟨C8, G2⟩
  iunfold stk at O7 C0 C4 C8
  icases O7 with ⟨%ob7, %hob7, O7⟩
  icases C0 with ⟨%c0, %hc0, C0⟩
  icases C4 with ⟨%c4, %hc4, C4⟩
  icases C8 with ⟨%c8, %hc8, C8⟩
  ihave O7 := memBytes_addr (show s.toNat - 48 + 16 = (s - 32).toNat by omega) $$ O7
  ihave C0 := memBytes_addr (show s.toNat - 48 + 16 + 12 + 4 = (s - 32).toNat + 16 by omega) $$ C0
  ihave C4 := memBytes_addr (show s.toNat - 48 + 16 + 12 + 4 + 4 = (s - 32).toNat + 20 by omega) $$ C4
  ihave C8 := memBytes_addr (show s.toNat - 48 + 16 + 12 + 4 + 4 + 4 = (s - 32).toNat + 24 by omega) $$ C8
  ihave #S845 := f845_spec (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    (s - 32) c (s - 32 + 16) ptr cap idx maxP hl live F (w ++ rest) ob7
    (by omega) hob7 (by omega) hptr hcap (by omega) (by omega) (by simp; omega) hlive hr $$ HR
  simp only [f841]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  rw [add_sub_left, hlt5]
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
  repeat mstep
  mstep [C8]
  repeat mstep
  mstep [C4]
  repeat mstep
  mstep [Hp]
  mstep [C0]
  repeat mstep
  mcall S845 using [Hg Lo Hvt Hinv C0 C4 Hbs O7]
  · iunfold pre845
    ihave Lo := stk_addr (show s.toNat - 48 = (s - 32).toNat - 16 by omega) $$ Lo
    ihave C0 := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by omega) $$ C0
    ihave C4 := memBytes_addr (show (s - 32).toNat + 20 = (s - 32 + 16).toNat + 4 by omega) $$ C4
    iframe Hg Lo Hvt Hinv C0 C4 Hbs O7
    ipureintro; rfl
  iunfold post845 at HQ
  icases HQ with ⟨%hrs, %q, Hg, Lo, Hvt, C0, C4, Q0, Q4, Q8, HA⟩
  subst hrs
  iunfold reallocated at HA
  icases HA with ⟨%⟨hq0, hqb⟩, HH, Hq, %junk, %hjunk, Hj⟩
  mcredits (80 * cfg.regularOpCost + M + R)
  repeat mstep
  mstep [Q8]
  repeat mstep
  mstep [Q4]
  repeat mstep
  mstep [Q0]
  repeat mstep
  mstep [Hp]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  -- the buffer: `w`, then `rest ++ junk`, of which the first `k` bytes are overwritten
  icases splitB (a := q.toNat) (b := q.toNat + w.length) w rest rfl $$ Hq with ⟨Hw, Hr⟩
  ihave Hr := joinB (a := q.toNat + w.length) (b := q.toNat + cap.toNat) rest junk (by omega) $$ [Hr Hj]
  · iframe Hr Hj
  icases U128From.memBytes_split n (q.toNat + w.length) k.toNat (rest ++ junk) (by simp; omega) $$ Hr
    with ⟨Ho, Ht⟩
  have hql : (q + UInt32.ofNat w.length).toNat = q.toNat + w.length := by
    rw [UInt32.toNat_add, hwl]; omega
  have S951 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
      (MemCpy.pre n (q + UInt32.ofNat w.length) p k ((rest ++ junk).take k.toNat) sb) (fun _ => M)
      (MemCpy.post n (q + UInt32.ofNat w.length) p sb) := by
    rw [← hM]
    exact MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg (q + UInt32.ofNat w.length) p k
      ((rest ++ junk).take k.toNat) sb (by simp; omega) hsb (by omega) hp
  ihave Ho := memBytes_addr (show q.toNat + w.length = (q + UInt32.ofNat w.length).toNat by omega) $$ Ho
  mcall S951 using [Ho Hsb]
  · iunfold MemCpy.pre
    iframe Ho Hsb
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Ho, Hsb⟩
  subst hrs
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  rw [show s - 32 + 32 = s by simp]
  mstep [Hg]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iunfold gPost
  iexists q
  iframe Hg Hvt Hp Hcap Hsb
  isplitl [Lo Q0 Q4 Q8 G1 C0 C4 C8 G2]
  · ihave Lo := stk_addr (show (s - 32).toNat - 16 = s.toNat - 48 by omega) $$ Lo
    ihave Q0 := stk_word n _ 0 $$ Q0
    ihave Q4 := stk_word n _ q $$ Q4
    ihave Q8 := stk_word n _ _ $$ Q8
    ihave C0 := stk_word n _ ptr $$ C0
    ihave C4 := stk_word n _ cap $$ C4
    ihave C8 := stk_word n _ 1 $$ C8
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [Q0 Q4]
    · iframe Q0 Q4
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 8) (k1 := 8) (k2 := 4) (k := 12) rfl rfl $$ [Q Q8]
    · iframe Q Q8
    ihave Q := stkJ (a := (s - 32).toNat) (b := s.toNat - 48 + 16 + 12) (k1 := 12) (k2 := 4) (k := 16) (by omega) rfl $$ [Q G1]
    · iframe Q G1
    ihave C := stkJ (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [C0 C4]
    · iframe C0 C4
    ihave C := stkJ (a := (s - 32 + 16).toNat) (b := (s - 32).toNat + 24) (k1 := 8) (k2 := 4) (k := 12) (by omega) rfl $$ [C C8]
    · iframe C C8
    ihave C := stkJ (a := (s - 32 + 16).toNat) (b := s.toNat - 48 + 16 + 12 + 4 + 4 + 4 + 4) (k1 := 12) (k2 := 4) (k := 16) (by omega) rfl $$ [C G2]
    · iframe C G2
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32 + 16).toNat) (k1 := 16) (k2 := 16) (k := 32) (by omega) rfl $$ [Q C]
    · iframe Q C
    iapply stkJ (a := s.toNat - 48) (b := (s - 32).toNat) (k1 := 16) (k2 := 32) (k := 48) (by omega) rfl
    iframe Lo Q
  isplitl [Hlen]
  · iapply (show (n ↦[i32][ v.toNat + 8 ] (UInt32.ofNat w.length + k) : IProp GF) ⊢
        n ↦[i32][ v.toNat + 8 ] UInt32.ofNat (w ++ sb).length by
      rw [show UInt32.ofNat w.length + k = UInt32.ofNat (w ++ sb).length by
        apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hwl]; simp only [UInt32.toNat_ofNat', List.length_append]
        omega]) $$ Hlen
  ihave Ho := memBytes_addr (show (q + UInt32.ofNat w.length).toNat = q.toNat + w.length by omega) $$ Ho
  isplitl [Hw Ho]
  · iapply joinB (a := q.toNat) (b := q.toNat + w.length) w sb rfl
    iframe Hw Ho
  isplitl [Ht]
  · iexists (rest ++ junk).drop k.toNat
    isplitr
    · ipureintro; simp; omega
    iapply memBytes_addr (show q.toNat + w.length + k.toNat = q.toNat + (w ++ sb).length by simp; omega) $$ Ht
  iunfold grownV
  iframe HH
  ipureintro; exact ⟨hq0, hqb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<&mut String as fmt::Write>::write_str(dp, p, k)`** (840) without room: 841's grow path on
the `String` at `*dp`, `Ok`. -/
theorem f840_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s dp v ptr cap p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (w rest sb : List UInt8) (hs : 48 ≤ s.toNat)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcap2 : cap.toNat < 2 ^ 27)
    (hwr : w.length + rest.length = cap.toNat) (hsb : sb.length = k.toNat)
    (hgrow : cap.toNat < w.length + k.toNat) (hlk : w.length + k.toNat < 2 ^ 27)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (UInt32.ofNat w.length + k))) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f840 Cg
        (fun args => iprop(⌜args = [.i32 dp, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗
          gPre n g gt s v ptr cap p idx ta (A 578) maxP hl live F w rest sb))
        (fun _ => 10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f841 [.i32 0, .i32 0, .i32 0]) +
          (300 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
            cost154 cfg F cap (growCap cap (UInt32.ofNat w.length + k))))
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗
          gPost n g gt s v ptr cap (growCap cap (UInt32.ofNat w.length + k)) p idx ta (A 578) maxP hl live F w sb)) := by
  iintro #Hk
  ihave #S841 := f841_grow cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s v ptr cap
    p k idx maxP hl live F w rest sb hs hv hptr hcap hcap2 hwr hsb hgrow hlk hp hlive hr $$ Hk
  iunfold strCode at Hk
  icases Hk with ⟨#HR, -, #H841⟩
  iunfold reallocCode at HR
  icases HR with ⟨#H, -⟩
  iunfold AllocTwo.code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha841 := hm.funcs 841 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hK : 300 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
    cost154 cfg F cap (growCap cap (UInt32.ofNat w.length + k)) = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hd, HP⟩
  subst hargs
  simp only [f840]
  mstep; mstep [Hd]
  repeat mstep
  mcall S841 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hd HQ
  ipureintro; rw [htype]; rfl

end Spec

end WNear.Binary.StrSinkGrow
