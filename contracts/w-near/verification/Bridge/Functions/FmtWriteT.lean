import Bridge.Functions.FmtWriteN

/-!
# `core::fmt::write` (872) with a trailing piece: `k + 1` pieces and `k` arguments

`write!(f, "'{}', ", x)` builds `Arguments { pieces: ["'", "', "], fmt: None, args: [x] }`: one
piece more than arguments. 872 runs `FmtWriteN.f872_gen`'s loop on `n = min(pieces.len, args.len)
= k`; after the loop `pieces.len = k + 1 > n`, so it writes the trailing piece `pieces[k]`:

```
     pieces.len ≤ n ? skip : (vtab.write_str)(*(sp + 32), pieces[n])   call_indirect type 15
     Ok (0); sp += 48
```

This file is `FmtWriteN` with the pieces' count `kp = k + 1` (the local 6, read only after the
loop) apart from the arguments' count `k`: the frame `fr872t`, the loop's invariant `inv872t`, the
`Arguments` `argsT`, and `Hyp872T` (`Hyp872` with the sink's `write_str` and the accessor for all
`k + 1` pieces). `f872_tr`: the writes `St 0 → … → St (2k + 1)`, at `costT` (`costN` and one more
write: `40` `regular_op_cost`s, the sink's activation and `Ka`). As in `FmtWriteN`, the proof is
split in three (`tail872t_spec`, `iter872t`, `f872_tr`), and the address of `pieces[k]` (the local
`pp + (k << 3)`) is generalized before the load.
-/

namespace WNear.Binary.FmtWriteT

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtWrite (act3 act2 i64_fmt_init frame_open frame_close)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.FmtGrow (mwpi_select')
open WNear.Binary.FmtWriteN (fmtrP mwpi_loop_dep dec_one dec_more sub4_toNat dec_toNat dec_zero body872 tail872)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `Arguments` at `ar`: `kp` pieces at `pp`, `fmt: None`, `k` arguments at `argp`. -/
def argsT (n : Nat) (ar pp argp kp k : UInt32) : IProp GF :=
  iprop(n ↦[i32][ ar.toNat ] pp ∗ n ↦[i32][ ar.toNat + 4 ] kp ∗ n ↦[i32][ ar.toNat + 8 ] 0 ∗
    n ↦[i32][ ar.toNat + 16 ] argp ∗ n ↦[i32][ ar.toNat + 20 ] k)

/-- The cost of 872 on `k + 1` pieces and `k` arguments. -/
def costT (cfg : WasmConfig) (codeA : Func) (Ka KB k : Nat) : Nat :=
  100 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) + Ka +
    k * (60 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) +
      Ka + KB) +
    (40 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) + Ka)

/-- The loop's frame at the argument `j`. -/
abbrev fr872t (inst : Nat) (mi : ModuleInst) (x0 l1 c sp y pp kp k l7 : UInt32) : Frame :=
  ⟨#[.i32 x0, .i32 l1, .i32 c, .i32 sp, .i32 y, .i32 pp, .i32 kp, .i32 l7, .i32 k, .i32 0, .i32 0, .i32 0],
    inst, mi⟩

/-- The loop's invariant at the argument `j < k`: the pieces `0..j` and the arguments `0..j-1`
written (`Res (2j + 1)`), credits for the `k - j` iterations left. -/
def inv872t (inst : Nat) (mi : ModuleInst) (Cg P R0 : Nat) (kp k pp argp sp : UInt32)
    (Res : Nat → IProp GF) : List Value → Frame → IProp GF := fun X fr =>
  iprop(∃ (j : Nat) (x0 l1 c y l7 : UInt32), ⌜X = [] ∧ fr = fr872t inst mi x0 l1 c sp y pp kp k l7 ∧
      j < k.toNat ∧ x0.toNat = pp.toNat + 12 + 8 * j ∧ c.toNat = k.toNat - j ∧
      y.toNat = argp.toNat + 8 * j⌝ ∗
    credits Cg ((k.toNat - j) * P + R0) ∗ Res (2 * j + 1))

/-- The frame of 872 between the writes: the stack word, the `Formatter` (`fmtrP`), the frame's
other bytes, the `Arguments`, the arrays `M` and the state `St i`. -/
def base872t (n g ta : Nat) (gt : GlobalType) (s data vtab idx : UInt32) (a : Nat) (ar pp argp kp k : UInt32)
    (M : IProp GF) (St : Nat → IProp GF) (i : Nat) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ fmtrP n ta (s - 48 + 8) data vtab idx a ∗
    (stk n (s - 48).toNat 8 ∗ stk n ((s - 48).toNat + 12) 4 ∗ stk n ((s - 48).toNat + 20) 4 ∗
      stk n ((s - 48).toNat + 28) 4 ∗ stk n ((s - 48).toNat + 40) 1 ∗ stk n ((s - 48).toNat + 41) 7) ∗
    argsT n ar pp argp kp k ∗ M ∗ St i)

/-- The loop's exit, past the last argument: from any locals, `R0` credits and `base872t (2k)`. -/
def exit872t (inst : Nat) (mi : ModuleInst) (Cg R0 : Nat) (sp pp kp k : UInt32) (B : IProp GF)
    (Φ : Post NearState GF) : IProp GF :=
  iprop(∀ x0 l1 y l7, credits Cg R0 -∗ B -∗ Φ.br 1 [] (fr872t inst mi x0 l1 0 sp y pp kp k l7))

/-- What 872 asks of its callees and of the arrays: the accessors of `M`, the code, the
specifications of the sink's `write_str` per piece and of the formatters per argument. -/
structure Hyp872T (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (n g ta Cg : Nat)
    (gt : GlobalType) (s data vtab idx pp argp k : UInt32) (pptr plen vp fi : Nat → UInt32)
    (b : Nat → Nat) (codeB : Nat → Func) (a : Nat) (codeA : Func) (C M : IProp GF)
    (St : Nat → IProp GF) (Ka Kb KB : Nat) : Prop where
  hMp : ∀ j, j < k.toNat + 1 → M ⊢ n ↦[i32][ pp.toNat + 8 * j ] pptr j ∗
    n ↦[i32][ pp.toNat + 8 * j + 4 ] plen j ∗
    (n ↦[i32][ pp.toNat + 8 * j ] pptr j ∗ n ↦[i32][ pp.toNat + 8 * j + 4 ] plen j -∗ M)
  hMa : ∀ j, j < k.toNat → M ⊢ n ↦[i32][ argp.toNat + 8 * j ] vp j ∗
    n ↦[i32][ argp.toNat + 8 * j + 4 ] fi j ∗ ta ↦[wt][ (fi j).toNat ] Ref.func (b j) ∗
    (n ↦[i32][ argp.toNat + 8 * j ] vp j ∗ n ↦[i32][ argp.toNat + 8 * j + 4 ] fi j ∗
      ta ↦[wt][ (fi j).toNat ] Ref.func (b j) -∗ M)
  hCa : C ⊢ inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst codeA
  hSa : ∀ j, j < k.toNat + 1 → C ⊢ MFunSpec cfg lim (d + 1) types[15]! inst mi codeA Cg
    (fun args => iprop(⌜args = [.i32 data, .i32 (pptr j), .i32 (plen j)]⌝ ∗
      g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ St (2 * j)))
    (fun _ => Ka) (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ St (2 * j + 1)))
  hBf : ∀ j, j < k.toNat → C ⊢ b j ↪[wf] FuncInst.wasm types[13]! inst (codeB j)
  hSb : ∀ j, j < k.toNat → C ⊢ MFunSpec cfg lim (d + 1) types[13]! inst mi (codeB j) Cg
    (fun args => iprop(⌜args = [.i32 (vp j), .i32 (s - 48 + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗
      fmtrP n ta (s - 48 + 8) data vtab idx a ∗ St (2 * j + 1)))
    (fun _ => Kb) (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗
      fmtrP n ta (s - 48 + 8) data vtab idx a ∗ St (2 * j + 2)))
  hKB : ∀ j, j < k.toNat →
    activationGas cfg.regularOpCost (entryLocals (codeB j) [.i32 0, .i32 0]) + Kb ≤ KB

/-- `base872t` and the exit, carried by the loop. -/
def res872t (n g ta : Nat) (gt : GlobalType) (s data vtab idx : UInt32) (a : Nat) (ar pp argp kp k : UInt32)
    (M : IProp GF) (St : Nat → IProp GF) (inst : Nat) (mi : ModuleInst) (Cg R0 : Nat)
    (Φ : Post NearState GF) (i : Nat) : IProp GF :=
  iprop(base872t n g ta gt s data vtab idx a ar pp argp kp k M St i ∗
    exit872t inst mi Cg R0 (s - 48) pp kp k (base872t n g ta gt s data vtab idx a ar pp argp kp k M St (2 * k.toNat)) Φ)

set_option maxHeartbeats 16000000 in
/-- **The piece `j + 1`** and back to the loop's invariant at `j + 1`. -/
theorem tail872t_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s data vtab ar pp argp idx kp k : UInt32) (hs : 48 ≤ s.toNat)
    (hpp : pp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32) (hargp : argp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32)
    (pptr plen vp fi : Nat → UInt32) (b : Nat → Nat) (codeB : Nat → Func) (a : Nat) (codeA : Func)
    (C : IProp GF) [Persistent C] (M : IProp GF) (St : Nat → IProp GF) (Ka Kb KB : Nat)
    (H : Hyp872T cfg lim d inst mi n g ta Cg gt s data vtab idx pp argp k pptr plen vp fi b codeB a codeA C M St
      Ka Kb KB)
    (ACa P R0 : Nat) (hACa : activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) = ACa)
    (Φ : Post NearState GF) (j : Nat) (x0 l1 c y l7 : UInt32) (hj1 : j + 1 < k.toNat)
    (hx0 : x0.toNat = pp.toNat + 12 + 8 * j) (hc : c.toNat = k.toNat - (j + 1))
    (hy : y.toNat = argp.toNat + 8 * j) (Z : Nat) (hZ : (k.toNat - (j + 1)) * P + R0 = Z)
    (es : List Instr) (hes : es = tail872) :
    C ∗ credits Cg (43 * cfg.regularOpCost + (ACa + Ka + Z)) ∗
      res872t n g ta gt s data vtab idx a ar pp argp kp k M St inst mi Cg R0 Φ (2 * j + 2)
      ⊢ mwpi cfg lim d (fr872t inst mi x0 l1 c (s - 48) y pp kp k l7) [] es (Post.mloop cfg Cg 0 []
        (inv872t inst mi Cg P R0 kp k pp argp (s - 48) (res872t n g ta gt s data vtab idx a ar pp argp kp k M St inst mi Cg R0 Φ))
        Φ) := by
  iintro ⟨#C, Hc, HR⟩
  ihave ⟨#Hi, #Ha⟩ := H.hCa $$ C
  have hn := hm.mem
  have hta := hm.table
  have hty15 : types[15]! = mi.types[15]! := by rw [hm.types]
  have hsp : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlt := s.toNat_lt
  have hf8 : (s - 48 + 8).toNat = (s - 48).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  generalize hW : ACa + Ka + Z = W
  iunfold res872t, base872t at HR
  icases HR with ⟨⟨Hg, HF, HJ, HA, HM, HS⟩, HEx⟩
  icases H.hMp (j + 1) (by omega) $$ HM with ⟨Q0, Q4, HMw⟩
  iunfold fmtrP, fmtr at HF
  icases HF with ⟨⟨F0, F8, F24, F28, V12, Ht⟩, F16⟩
  ihave #Saj := H.hSa (j + 1) (by omega) $$ C
  subst hes
  simp only [fr872t, tail872]
  repeat mstep
  have hx4 := sub4_toNat x0 (pp.toNat + 8 * (j + 1)) (by omega)
  generalize x0 + 4294967292 = x4 at hx4 ⊢
  mstep [Q4]
  repeat mstep
  mstep [F24]
  repeat mstep
  mstep [Q0] with exact (Nat.add_zero _).trans hx4
  repeat mstep
  mstep [F28]
  mstep [V12]
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 (pptr (j + 1)), Value.i32 (plen (j + 1)), Value.i32 idx] =
    [Value.i32 data, Value.i32 (pptr (j + 1)), Value.i32 (plen (j + 1))] ++ [Value.i32 idx] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 8 * cfg.regularOpCost + Z) 15 0 ta idx a types[15]!
    inst mi codeA [.i32 data, .i32 (pptr (j + 1)), .i32 (plen (j + 1))] _ (fun _ => Ka) _ hta hty15 rfl (by omega)
  rw [act3, hACa]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Ht]; · iexact Ht
  isplitr; · iexact Ha
  isplitr; · iexact Hi
  isplitr; · iexact Saj
  isplitl [HS Hg]
  · isplitr; · ipureintro; rfl
    iframe Hg; iexact HS
  inext
  iintro %rs Ht Hc HQ
  icases HQ with ⟨%hrs, Hg, HS⟩
  subst hrs
  mstep_post
  repeat mstep
  simp only [Post.mloop]
  iapply pure_pay_intro'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨by simp, by omega⟩
  inext
  iintro Hc
  ihave HM := HMw $$ [Q0 Q4]
  · iframe Q0; iexact Q4
  iunfold inv872t
  iexists j + 1, x0 + 8, x4, c, y + 8, plen (j + 1)
  isplitr
  · ipureintro
    refine ⟨by simp, rfl, hj1, ?_, ?_, ?_⟩
    · rw [UInt32.toNat_add]; simp; omega
    · omega
    · rw [UInt32.toNat_add]; simp; omega
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  iunfold res872t, base872t
  iframe HEx Hg HJ HA HM HS
  iunfold fmtrP, fmtr
  iframe F0 F8 F24 F28 V12 Ht F16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **One iteration of 872's loop**: the argument `j`, then the piece `j + 1` and back to the loop,
or (past the last argument) the exit. -/
theorem iter872t (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s data vtab ar pp argp idx kp k : UInt32) (hs : 48 ≤ s.toNat)
    (hpp : pp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32) (hargp : argp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32)
    (pptr plen vp fi : Nat → UInt32) (b : Nat → Nat) (codeB : Nat → Func) (a : Nat) (codeA : Func)
    (C : IProp GF) [Persistent C] (M : IProp GF) (St : Nat → IProp GF) (Ka Kb KB : Nat)
    (H : Hyp872T cfg lim d inst mi n g ta Cg gt s data vtab idx pp argp k pptr plen vp fi b codeB a codeA C M St
      Ka Kb KB)
    (ACa P R0 : Nat) (hACa : activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) = ACa)
    (hP : 60 * cfg.regularOpCost + ACa + Ka + KB = P) (Φ : Post NearState GF) (es : List Instr)
    (hes : es = body872) :
    C ⊢ □ ∀ (X : List Value) (fr : Frame),
      inv872t inst mi Cg P R0 kp k pp argp (s - 48)
        (res872t n g ta gt s data vtab idx a ar pp argp kp k M St inst mi Cg R0 Φ) X fr -∗
      mwpi cfg lim d fr X es (Post.mloop cfg Cg 0 []
        (inv872t inst mi Cg P R0 kp k pp argp (s - 48) (res872t n g ta gt s data vtab idx a ar pp argp kp k M St inst mi Cg R0 Φ))
        Φ) := by
  subst hes
  iintro #C
  ihave ⟨#Hi, #Ha⟩ := H.hCa $$ C
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hty15 : types[15]! = mi.types[15]! := by rw [hm.types]
  have hty13 : types[13]! = mi.types[13]! := by rw [hm.types]
  have hsp : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlt := s.toNat_lt
  have hf8 : (s - 48 + 8).toNat = (s - 48).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  imodintro
  iintro %X %fr HI
  iunfold inv872t at HI
  icases HI with ⟨%j, %x0, %l1, %c, %y, %l7, %⟨hX, hfr, hj, hx0, hc, hy⟩, Hc, HR⟩
  subst hX hfr
  simp only [fr872t, body872]
  iunfold res872t, base872t at HR
  icases HR with ⟨⟨Hg, HF, HJ, HA, HM, HS⟩, HEx⟩
  icases H.hMa j hj $$ HM with ⟨G0, G4, Gt, HMw⟩
  ihave #Sbj := H.hSb j hj $$ C
  ihave #Hbj := H.hBf j hj $$ C
  have hKBj := H.hKB j hj
  rw [show (k.toNat - j) * P + R0 = P + ((k.toNat - (j + 1)) * P + R0) by
      rw [show k.toNat - j = (k.toNat - (j + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]; omega]
  generalize hZ : (k.toNat - (j + 1)) * P + R0 = Z
  repeat mstep
  mstep [G0]
  repeat mstep
  mstep [G4]
  iapply mwpi_cons
  rw [show [Value.i32 (vp j), Value.i32 (s - 48 + 8), Value.i32 (fi j)] =
    [Value.i32 (vp j), Value.i32 (s - 48 + 8)] ++ [Value.i32 (fi j)] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 50 * cfg.regularOpCost + ACa + Ka + Z) 13 0 ta (fi j) (b j)
    types[13]! inst mi (codeB j) [.i32 (vp j), .i32 (s - 48 + 8)] _ (fun _ => Kb) _ hta hty13 rfl (by omega)
  rw [act2]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Gt]; · iexact Gt
  isplitr; · iexact Hbj
  isplitr; · iexact Hi
  isplitr; · iexact Sbj
  isplitl [HS Hg HF]
  · isplitr; · ipureintro; rfl
    iframe Hg HF; iexact HS
  inext
  iintro %rs Gt Hc HQ
  icases HQ with ⟨%hrs, Hg, HF, HS⟩
  subst hrs
  ihave HM := HMw $$ [G0 G4 Gt]
  · iframe G0 G4 Gt
  mstep_post
  mcredits (50 * cfg.regularOpCost + (ACa + Ka + Z))
  generalize hW : ACa + Ka + Z = W
  mstep; mstep; mstep; mstep; mstep; mstep
  by_cases hlast : j + 1 = k.toNat
  · rw [dec_one c (by omega), dec_zero c (by omega)]
    repeat mstep
    have h0 : k.toNat - (j + 1) = 0 := by omega
    rw [h0, Nat.zero_mul, Nat.zero_add] at hZ
    simp only [Post.mloop, List.nil_append]
    iunfold exit872t at HEx
    mcredits R0
    iapply HEx $$ Hc
    iframe Hg HF HJ HA HM
    rw [← hlast]; iexact HS
  · have hj1 : j + 1 < k.toNat := by omega
    rw [dec_more c (by omega)]
    have hc' := dec_toNat c (by omega)
    generalize c + 4294967295 = c' at hc' ⊢
    mstep
    iapply tail872t_spec cfg lim d inst mi A n g ta hm hd Cg gt s data vtab ar pp argp idx kp k hs hpp hargp
      pptr plen vp fi b codeB a codeA C M St Ka Kb KB H ACa P R0 hACa Φ j x0 l1 c' y l7 hj1 hx0 (by omega) hy Z hZ _ (by rfl)
    rw [← hW]
    iframe C Hc
    iunfold res872t, base872t
    iframe HEx Hg HF HJ HA HM HS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`core::fmt::write(data, vtab, ar)`** (872) on `fmt: None` with `k + 1` pieces and `k ≥ 1`
arguments (`Hyp872T`): piece `0`, then for each `j < k` the argument `j` and the piece `j + 1`; `Ok`. -/
theorem f872_tr (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s data vtab ar pp argp idx kp k : UInt32) (hk0 : 0 < k.toNat) (hkp : kp.toNat = k.toNat + 1)
    (hs : 48 ≤ s.toNat) (har : ar.toNat + 24 ≤ 2 ^ 32)
    (hpp : pp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32) (hargp : argp.toNat + 8 * k.toNat + 8 ≤ 2 ^ 32)
    (pptr plen vp fi : Nat → UInt32) (b : Nat → Nat) (codeB : Nat → Func) (a : Nat) (codeA : Func)
    (C : IProp GF) [Persistent C] (M : IProp GF) (St : Nat → IProp GF) (Ka Kb KB : Nat)
    (H : Hyp872T cfg lim d inst mi n g ta Cg gt s data vtab idx pp argp k pptr plen vp fi b codeB a codeA C M St
      Ka Kb KB) :
    C ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsT n ar pp argp kp k ∗ M ∗
          n ↦[i32][ vtab.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗ St 0))
        (fun _ => costT cfg codeA Ka KB k.toNat)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsT n ar pp argp kp k ∗ M ∗
          n ↦[i32][ vtab.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗ St (2 * k.toNat + 1))) := by
  iintro #C
  ihave ⟨#Hi, #Ha⟩ := H.hCa $$ C
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hty15 : types[15]! = mi.types[15]! := by rw [hm.types]
  have hty13 : types[13]! = mi.types[13]! := by rw [hm.types]
  have hsp : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlt := s.toNat_lt
  have hf8 : (s - 48 + 8).toNat = (s - 48).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u k kp) = 0 then Value.i32 k else Value.i32 kp) =
      Value.i32 k := by
    have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u k kp) = 0 := by
      simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]; omega
    simp [this]
  have hle0 : Numeric.bool (Numeric.irelop32 IRelOp.le_u kp k) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le]; omega
  simp only [costT]
  generalize hACa : activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) = ACa
  generalize hP : 60 * cfg.regularOpCost + ACa + Ka + KB = P
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HA, HM, V12, Ht, HS0⟩
  subst hargs
  iunfold argsT at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  icases H.hMp 0 (by omega) $$ HM with ⟨P0, P4, HMw⟩
  ihave P0 := memBytes_addr (show pp.toNat + 8 * 0 = pp.toNat by omega) $$ P0
  ihave P4 := memBytes_addr (show pp.toNat + 8 * 0 + 4 = pp.toNat + 4 by omega) $$ P4
  ihave Hs := stk_addr (show s.toNat - 48 = (s - 48).toNat by omega) $$ Hs
  icases frame_open n (s - 48).toNat $$ Hs with ⟨X0, W8, W16, X20, W24, X28, W32, W36, B40, X41⟩
  iunfold stk at W8 W16 W24 W32 W36 B40
  icases W8 with ⟨%w8, %hw8, W8⟩
  icases W16 with ⟨%w16, %hw16, W16⟩
  icases W24 with ⟨%w24, %hw24, W24⟩
  icases W32 with ⟨%w32, %hw32, W32⟩
  icases W36 with ⟨%w36, %hw36, W36⟩
  icases B40 with ⟨%b40, %hb40, B40⟩
  simp only [f872]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep [W36]
  mstep; mstep; mstep [B40]
  mstep; mstep; mstep [W8]
  mstep; mstep; mstep [W32]
  mstep; mstep; mstep [W24]
  mstep; mstep; mstep [W16]
  rw [i64_fmt_init] at *
  repeat mstep
  mstep [A8]
  repeat mstep
  mstep [A0]
  repeat mstep
  mstep [A4]
  repeat mstep
  mstep [A20]
  repeat mstep
  msel
  simp only [hsel]
  have hkne : k ≠ 0 := by intro h; subst h; simp at hk0
  repeat mstep
  mstep [A16]
  repeat mstep
  mstep [P0]
  repeat mstep
  mstep [P4]
  repeat mstep
  mstep [V12]
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 (pptr 0), Value.i32 (plen 0), Value.i32 idx] =
    [Value.i32 data, Value.i32 (pptr 0), Value.i32 (plen 0)] ++ [Value.i32 idx] from rfl]
  ihave #Sa0 := H.hSa 0 (by omega) $$ C
  iapply mwpi_call_indirect_spec_args (R := 40 * cfg.regularOpCost + k.toNat * P + (40 * cfg.regularOpCost + ACa + Ka + R)) 15 0 ta idx a types[15]!
    inst mi codeA [.i32 data, .i32 (pptr 0), .i32 (plen 0)] _ (fun _ => Ka) _ hta hty15 rfl (by omega)
  rw [act3, hACa]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Ht]; · iexact Ht
  isplitr; · iexact Ha
  isplitr; · iexact Hi
  isplitr; · iexact Sa0
  isplitl [HS0 Hg]
  · isplitr; · ipureintro; rfl
    iframe Hg; iexact HS0
  inext
  iintro %rs Ht Hc HQ
  icases HQ with ⟨%hrs, Hg, HS1⟩
  subst hrs
  mstep_post
  repeat mstep
  -- the Formatter, as the arguments see it
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 48).toNat + 8) (bytes32 0) (bytes32 32)).1 $$ W8
    with ⟨F0, F4⟩
  ihave F4 := FmtU128.stk_of n _ 4 _ (by decide) $$ F4
  ihave F4 := stk_addr (show (s - 48).toNat + 8 + (bytes32 0).length = (s - 48).toNat + 12 by simp [bytes32]) $$ F4
  ihave B40 := FmtU128.stk_of n _ 1 _ (by decide) $$ B40
  ihave F0 := memBytes_addr (show (s - 48).toNat + 8 = (s - 48 + 8).toNat by omega) $$ F0
  ihave F8 := memBytes_addr (show (s - 48).toNat + 16 = (s - 48 + 8).toNat + 8 by omega) $$ W16
  ihave F16 := memBytes_addr (show (s - 48).toNat + 24 = (s - 48 + 8).toNat + 16 by omega) $$ W24
  ihave F24 := memBytes_addr (show (s - 48).toNat + 32 = (s - 48 + 8).toNat + 24 by omega) $$ W32
  ihave F28 := memBytes_addr (show (s - 48).toNat + 36 = (s - 48 + 8).toNat + 28 by omega) $$ W36
  ihave HF : fmtrP n ta (s - 48 + 8) data vtab idx a $$ [F0 F8 F16 F24 F28 V12 Ht]
  · iunfold fmtrP, fmtr; iframe F0 F8 F16 F24 F28 V12 Ht
  ihave HM := HMw $$ [P0 P4]
  · iframe P0; iexact P4
  iapply mwpi_cons
  iapply mwpi_loop_dep (Cg := Cg) (R := k.toNat * P + (20 * cfg.regularOpCost + (40 * cfg.regularOpCost + ACa + Ka + R)))
    (I := fun Φ => inv872t inst mi Cg P (20 * cfg.regularOpCost + (40 * cfg.regularOpCost + ACa + Ka + R)) kp k pp argp (s - 48)
      (res872t n g ta gt s data vtab idx a ar pp argp kp k M St inst mi Cg (20 * cfg.regularOpCost + (40 * cfg.regularOpCost + ACa + Ka + R)) Φ)) _ _ rfl
  isplitr
  · ihave #It := iter872t cfg lim d inst mi A n g ta hm hd Cg gt s data vtab ar pp argp idx kp k hs hpp hargp
      pptr plen vp fi b codeB a codeA C M St Ka Kb KB H ACa P (20 * cfg.regularOpCost + (40 * cfg.regularOpCost + ACa + Ka + R)) hACa hP _ body872 rfl $$ C
    imodintro
    iintro %X %l HI
    iapply It $$ HI
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  inext
  iintro Hc
  iunfold inv872t
  iexists 0, pp + 12, vtab, k, argp, 0
  isplitr
  · ipureintro
    refine ⟨rfl, rfl, hk0, ?_, by simp, by simp⟩
    rw [UInt32.toNat_add]; simp; omega
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; simp
  iunfold res872t, base872t
  iframe Hg HF HM HS1
  isplitl [X0 F4 X20 X28 B40 X41 A0 A4 A8 A16 A20]
  · isplitl [X0 F4 X20 X28 B40 X41]
    · iframe X0 F4 X20 X28 B40 X41
    iunfold argsT
    iframe A0 A4 A8 A16 A20
  iunfold exit872t
  iintro %x0 %l1 %y %l7 Hc HB
  mctrl_norm
  repeat mpay
  repeat mstep
  icases HB with ⟨Hg, HF, ⟨X0, F4, X20, X28, B40, X41⟩, HA, HM, HS⟩
  iunfold fmtrP, fmtr at HF
  icases HF with ⟨⟨F0, F8, F24, F28, V12, Ht⟩, F16⟩
  ihave F24 := memBytes_addr (show (s - 48 + 8).toNat + 24 = (s - 48).toNat + 32 by omega) $$ F24
  ihave F28 := memBytes_addr (show (s - 48 + 8).toNat + 28 = (s - 48).toNat + 36 by omega) $$ F28
  icases H.hMp k.toNat (by omega) $$ HM with ⟨Q0, Q4, HMw⟩
  ihave #Sak := H.hSa k.toNat (by omega) $$ C
  repeat mstep
  mstep [F24]
  repeat mstep
  have hx8 : (pp + k <<< (3 % 32)).toNat = pp.toNat + 8 * k.toNat := by
    simp [UInt32.toNat_add, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  generalize pp + k <<< (3 % 32) = x8 at hx8 ⊢
  mstep [Q0] with exact (Nat.add_zero _).trans hx8
  mstep
  mstep [Q4] with exact (by omega : x8.toNat + 4 = pp.toNat + 8 * k.toNat + 4)
  repeat mstep
  mstep [F28]
  mstep [V12]
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 (pptr k.toNat), Value.i32 (plen k.toNat), Value.i32 idx] =
    [Value.i32 data, Value.i32 (pptr k.toNat), Value.i32 (plen k.toNat)] ++ [Value.i32 idx] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 20 * cfg.regularOpCost + R) 15 0 ta idx a types[15]!
    inst mi codeA [.i32 data, .i32 (pptr k.toNat), .i32 (plen k.toNat)] _ (fun _ => Ka) _ hta hty15 rfl (by omega)
  rw [act3, hACa]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Ht]; · iexact Ht
  isplitr; · iexact Ha
  isplitr; · iexact Hi
  isplitr; · iexact Sak
  isplitl [HS Hg]
  · isplitr; · ipureintro; rfl
    iframe Hg; iexact HS
  inext
  iintro %rs Ht Hc HQ
  icases HQ with ⟨%hrs, Hg, HS⟩
  subst hrs
  mstep_post
  repeat mstep
  ihave HM := HMw $$ [Q0 Q4]
  · iframe Q0; iexact Q4
  rw [show s - 48 + 48 = s by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  iframe Hc Hg HA HM V12 Ht HS
  isplitr; · ipureintro; rw [htype]; rfl
  ihave F0 := memBytes_addr (show (s - 48 + 8).toNat = (s - 48).toNat + 8 by omega) $$ F0
  ihave F8 := memBytes_addr (show (s - 48 + 8).toNat + 8 = (s - 48).toNat + 16 by omega) $$ F8
  ihave F16 := memBytes_addr (show (s - 48 + 8).toNat + 16 = (s - 48).toNat + 24 by omega) $$ F16
  ihave F0 := stk_word n _ _ $$ F0
  ihave W8 := stk_join n ((s - 48).toNat + 8) 4 4 $$ [F0 F4]
  · iframe F0; iexact F4
  iapply stk_addr (show (s - 48).toNat = s.toNat - 48 by omega)
  iapply frame_close n (s - 48).toNat
  iframe X0 X20 X28 X41 W8 B40
  isplitl [F8]; · iapply stk_word $$ F8
  isplitl [F16]; · iapply stk_word $$ F16
  isplitl [F24]; · iapply stk_word $$ F24
  iapply stk_word $$ F28

end Spec

end WNear.Binary.FmtWriteT
