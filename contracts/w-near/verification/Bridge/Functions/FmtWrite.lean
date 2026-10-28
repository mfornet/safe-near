import Bridge.Functions.FmtDisplay
import Bridge.Functions.FmtSink
import Bridge.Functions.ResultExpect
import Binary.Code.Part13
import Binary.Code.Part18

/-!
# `core::fmt::write` (872) and `Write::write_fmt` (746) with one argument (M5)

`to_string()` of a `u128` (385) formats `Arguments { pieces: [""], fmt: None, args: [(&&u128, 92)] }`
into an empty `String` through `Write::write_fmt` (746), which copies the `Arguments` to its
frame and calls `core::fmt::write(&mut &mut String, 1065404, &args)` (872). On `fmt: None` with
one piece and one argument, 872:

```
872  sp -= 48; the Formatter at sp + 8: flags 0, fill ' ', align 3, width/precision None,
     buf (data, vtab) at sp + 32
     fmt = None ⇒ n = min(pieces.len, args.len) = 1
     (vtab.write_str)(data, pieces[0])                 call_indirect type 15
     loop: (args[0].fmt)(args[0].value, sp + 8)        call_indirect type 13
           n - 1 = 0 ⇒ out of the loop
     pieces.len = 1 ≤ 1 ⇒ no trailing piece; Ok (0); sp += 48
746  sp -= 32; *(sp + 4) = string; the Arguments copied to sp + 8; write(sp + 4, 1065404, sp + 8)
```

`f872_one` is parametric in the two indirect callees: the piece's `write_str` (code `a`,
`P1 → Q1`) and the argument's formatter (code `b`, `Q1 → Q2`, with the `Formatter` as
`FmtPad.fmtr` at `sp + 8`). The loop runs once (`mwpi_loop_once`).
-/

namespace WNear.Binary.FmtWrite

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.FmtGrow (mwpi_select')

section Loop

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF} {Cg R : Nat}

/-- A loop whose body never branches back to it: the body proved for any invariant. -/
theorem mwpi_loop_once (bt : BlockType) (body : List Instr) (hp : (Exec.blockType f.mi bt).params = []) :
    credits Cg (cfg.regularOpCost + R) ∗
      (credits Cg R -∗ ∀ I, mwpi cfg lim d f [] body (Post.mloop cfg Cg 0 [] I Φ))
      ⊢ mwpi cfg lim d f [] [.loop bt body] Φ := by
  iintro ⟨Hc, HB⟩
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := R)
    (I := fun X g => iprop(⌜X = [] ∧ g = f⌝ ∗ ∀ I, mwpi cfg lim d f [] body (Post.mloop cfg Cg 0 [] I Φ)))
    bt body hp
  isplitr
  · imodintro
    iintro %X %l ⟨%⟨hX, hl⟩, HI⟩
    subst hX
    rw [hl]
    iapply HI
  iframe Hc
  inext
  iintro Hc
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iapply HB $$ Hc

end Loop

theorem act3 (c : Nat) (code : Func) (a b e : UInt32) :
    activationGas c (entryLocals code [.i32 a, .i32 b, .i32 e]) =
      activationGas c (entryLocals code [.i32 0, .i32 0, .i32 0]) := by
  simp [activationGas, entryLocals]

theorem act2 (c : Nat) (code : Func) (a b : UInt32) :
    activationGas c (entryLocals code [.i32 a, .i32 b]) =
      activationGas c (entryLocals code [.i32 0, .i32 0]) := by
  simp [activationGas, entryLocals]

theorem i64_fmt_init : storeBytes (.i64 137438953472) 8 = bytes32 0 ++ bytes32 32 := by decide

section Frame

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 872's frame, in the pieces its body writes. -/
theorem frame_open (n a : Nat) :
    stk (GF := GF) n a 48 ⊢ stk n a 8 ∗ stk n (a + 8) 8 ∗ stk n (a + 16) 4 ∗ stk n (a + 20) 4 ∗
      stk n (a + 24) 4 ∗ stk n (a + 28) 4 ∗ stk n (a + 32) 4 ∗ stk n (a + 36) 4 ∗ stk n (a + 40) 1 ∗
      stk n (a + 41) 7 := by
  iintro H
  icases stk_split n a 8 40 $$ H with ⟨H0, H⟩
  icases stk_split n (a + 8) 8 32 $$ H with ⟨H1, H⟩
  icases stk_split n (a + 8 + 8) 4 28 $$ H with ⟨H2, H⟩
  icases stk_split n (a + 8 + 8 + 4) 4 24 $$ H with ⟨H3, H⟩
  icases stk_split n (a + 8 + 8 + 4 + 4) 4 20 $$ H with ⟨H4, H⟩
  icases stk_split n (a + 8 + 8 + 4 + 4 + 4) 4 16 $$ H with ⟨H5, H⟩
  icases stk_split n (a + 8 + 8 + 4 + 4 + 4 + 4) 4 12 $$ H with ⟨H6, H⟩
  icases stk_split n (a + 8 + 8 + 4 + 4 + 4 + 4 + 4) 4 8 $$ H with ⟨H7, H⟩
  icases stk_split n (a + 8 + 8 + 4 + 4 + 4 + 4 + 4 + 4) 1 7 $$ H with ⟨H8, H9⟩
  iframe H0 H1
  rw [show a + 8 + 8 = a + 16 by omega, show a + 16 + 4 = a + 20 by omega,
    show a + 20 + 4 = a + 24 by omega, show a + 24 + 4 = a + 28 by omega,
    show a + 28 + 4 = a + 32 by omega, show a + 32 + 4 = a + 36 by omega,
    show a + 36 + 4 = a + 40 by omega, show a + 40 + 1 = a + 41 by omega]
  iframe H2 H3 H4 H5 H6 H7 H8 H9

theorem frame_close (n a : Nat) :
    stk (GF := GF) n a 8 ∗ stk n (a + 8) 8 ∗ stk n (a + 16) 4 ∗ stk n (a + 20) 4 ∗
      stk n (a + 24) 4 ∗ stk n (a + 28) 4 ∗ stk n (a + 32) 4 ∗ stk n (a + 36) 4 ∗ stk n (a + 40) 1 ∗
      stk n (a + 41) 7 ⊢ stk n a 48 := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9⟩
  ihave H := stk_join n (a + 40) 1 7 $$ [H8 H9]
  · iframe H8; iexact H9
  ihave H := stk_join n (a + 36) 4 8 $$ [H7 H]
  · iframe H7; iexact H
  ihave H := stk_join n (a + 32) 4 12 $$ [H6 H]
  · iframe H6; iexact H
  ihave H := stk_join n (a + 28) 4 16 $$ [H5 H]
  · iframe H5; iexact H
  ihave H := stk_join n (a + 24) 4 20 $$ [H4 H]
  · iframe H4; iexact H
  ihave H := stk_join n (a + 20) 4 24 $$ [H3 H]
  · iframe H3; iexact H
  ihave H := stk_join n (a + 16) 4 28 $$ [H2 H]
  · iframe H2; iexact H
  ihave H := stk_join n (a + 8) 8 32 $$ [H1 H]
  · iframe H1; iexact H
  iapply stk_join n a 8 40
  iframe H0 H

end Frame

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `Arguments` at `ar` on the path: one piece at `pp`, `fmt: None`, one argument at `argp`. -/
def argsAt (n : Nat) (ar pp argp : UInt32) : IProp GF :=
  iprop(n ↦[i32][ ar.toNat ] pp ∗ n ↦[i32][ ar.toNat + 4 ] 1 ∗ n ↦[i32][ ar.toNat + 8 ] 0 ∗
    n ↦[i32][ ar.toNat + 16 ] argp ∗ n ↦[i32][ ar.toNat + 20 ] 1)

/-- The piece `(ptr0, len0)` at `pp` and the argument `(vp, fi)` at `argp`, its table entry. -/
def pieceArg (n ta : Nat) (pp ptr0 len0 argp vp fi : UInt32) (b : Nat) : IProp GF :=
  iprop(n ↦[i32][ pp.toNat ] ptr0 ∗ n ↦[i32][ pp.toNat + 4 ] len0 ∗ n ↦[i32][ argp.toNat ] vp ∗
    n ↦[i32][ argp.toNat + 4 ] fi ∗ ta ↦[wt][ fi.toNat ] Ref.func b)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`core::fmt::write(data, vtab, ar)`** (872) on `fmt: None`, one piece, one argument: the
piece's `write_str` (`P1 → Q1`), then the argument's formatter (`Q1 → Q2`) on the `Formatter`
at `sp + 8` (`sp = s - 48`); `Ok`. -/
theorem f872_one (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s data vtab ar pp argp ptr0 len0 vp fi idx : UInt32) (hs : 48 ≤ s.toNat)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (har : ar.toNat + 24 ≤ 2 ^ 32) (hpp : pp.toNat + 8 ≤ 2 ^ 32)
    (hargp : argp.toNat + 8 ≤ 2 ^ 32) (a b : Nat) (codeA codeB : Func) (P1 Q1 Q2 : IProp GF)
    (Ka Kb : Nat) :
    inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst codeA ∗
      b ↪[wf] FuncInst.wasm types[13]! inst codeB ∗
      MFunSpec cfg lim (d + 1) types[15]! inst mi codeA Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 ptr0, .i32 len0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ P1))
        (fun _ => Ka) (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ Q1)) ∗
      MFunSpec cfg lim (d + 1) types[13]! inst mi codeB Cg
        (fun args => iprop(⌜args = [.i32 vp, .i32 (s - 48 + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗
          fmtr n ta (s - 48 + 8) data vtab idx a ∗ Q1))
        (fun _ => Kb) (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗
          fmtr n ta (s - 48 + 8) data vtab idx a ∗ Q2))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsAt n ar pp argp ∗ pieceArg n ta pp ptr0 len0 argp vp fi b ∗
          n ↦[i32][ vtab.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗ P1))
        (fun _ => 100 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) + Ka +
          activationGas cfg.regularOpCost (entryLocals codeB [.i32 0, .i32 0]) + Kb)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsAt n ar pp argp ∗ pieceArg n ta pp ptr0 len0 argp vp fi b ∗
          n ↦[i32][ vtab.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗ Q2)) := by
  iintro ⟨#Hi, #Ha, #Hb, #Sa, #Sb⟩
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hty15 : types[15]! = mi.types[15]! := by rw [hm.types]
  have hty13 : types[13]! = mi.types[13]! := by rw [hm.types]
  have hsp : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlt := s.toNat_lt
  generalize hACa : activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) = ACa
  generalize hACb : activationGas cfg.regularOpCost (entryLocals codeB [.i32 0, .i32 0]) = ACb
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HA, HPA, V12, Ht, HP1⟩
  subst hargs
  iunfold argsAt at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  iunfold pieceArg at HPA
  icases HPA with ⟨P0, P4, G0, G4, Gt⟩
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
  repeat mstep
  mstep [A16]
  repeat mstep
  mstep [P0]
  repeat mstep
  mstep [P4]
  repeat mstep
  mstep [V12]
  simp only [ite_self]
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 ptr0, Value.i32 len0, Value.i32 idx] =
    [Value.i32 data, Value.i32 ptr0, Value.i32 len0] ++ [Value.i32 idx] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 41 * cfg.regularOpCost + ACb + Kb + R) 15 0 ta idx a types[15]!
    inst mi codeA [.i32 data, .i32 ptr0, .i32 len0] _ (fun _ => Ka) _ hta hty15 rfl (by omega)
  rw [act3, hACa]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Ht]; · iexact Ht
  isplitr; · iexact Ha
  isplitr; · iexact Hi
  isplitr; · iexact Sa
  isplitl [HP1 Hg]
  · iframe HP1 Hg; ipureintro; rfl
  inext
  iintro %rs Ht Hc HQ
  icases HQ with ⟨%hrs, Hg, HQ1⟩
  subst hrs
  mstep_post
  repeat mstep
  iapply mwpi_cons
  iapply mwpi_loop_once (R := 33 * cfg.regularOpCost + ACb + Kb + R) _ _ rfl
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  iintro Hc %I
  have hf8 : (s - 48 + 8).toNat = (s - 48).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 48).toNat + 8) (bytes32 0) (bytes32 32)).1 $$ W8
    with ⟨F0, F4⟩
  ihave F0 := memBytes_addr (show (s - 48).toNat + 8 = (s - 48 + 8).toNat by omega) $$ F0
  ihave F8 := memBytes_addr (show (s - 48).toNat + 16 = (s - 48 + 8).toNat + 8 by omega) $$ W16
  ihave F24 := memBytes_addr (show (s - 48).toNat + 32 = (s - 48 + 8).toNat + 24 by omega) $$ W32
  ihave F28 := memBytes_addr (show (s - 48).toNat + 36 = (s - 48 + 8).toNat + 28 by omega) $$ W36
  repeat mstep
  mstep [G0]
  repeat mstep
  mstep [G4]
  iapply mwpi_cons
  rw [show [Value.i32 vp, Value.i32 (s - 48 + 8), Value.i32 fi] =
    [Value.i32 vp, Value.i32 (s - 48 + 8)] ++ [Value.i32 fi] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 23 * cfg.regularOpCost + R) 13 0 ta fi b types[13]!
    inst mi codeB [.i32 vp, .i32 (s - 48 + 8)] _ (fun _ => Kb) _ hta hty13 rfl (by omega)
  rw [act2, hACb]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Gt]; · iexact Gt
  isplitr; · iexact Hb
  isplitr; · iexact Hi
  isplitr; · iexact Sb
  isplitl [HQ1 Hg F0 F8 F24 F28 V12 Ht]
  · iframe HQ1 Hg
    isplitr; · ipureintro; rfl
    iunfold fmtr
    iframe F0 F8 F24 F28 V12 Ht
  inext
  iintro %rs Gt Hc HQ
  icases HQ with ⟨%hrs, Hg, HF, HQ2⟩
  subst hrs
  mstep_post
  repeat mstep
  mloop_norm
  repeat mstep
  rw [show s - 48 + 48 = s by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  iunfold fmtr at HF
  icases HF with ⟨F0, F8, F24, F28, V12, Ht⟩
  iframe Hc Hg V12 Ht HQ2
  isplitr; · ipureintro; rw [htype]; rfl
  isplitl [X0 F0 F4 F8 X20 W24 X28 F24 F28 B40 X41]
  · ihave F0 := memBytes_addr (show (s - 48 + 8).toNat = (s - 48).toNat + 8 by omega) $$ F0
    ihave F8 := memBytes_addr (show (s - 48 + 8).toNat + 8 = (s - 48).toNat + 16 by omega) $$ F8
    ihave F24 := memBytes_addr (show (s - 48 + 8).toNat + 24 = (s - 48).toNat + 32 by omega) $$ F24
    ihave F28 := memBytes_addr (show (s - 48 + 8).toNat + 28 = (s - 48).toNat + 36 by omega) $$ F28
    ihave W8 := (memBytes_append (GF := GF) (H := NearState) n ((s - 48).toNat + 8) (bytes32 0) (bytes32 32)).2 $$ [F0 F4]
    · iframe F0; iexact F4
    ihave W8 := FmtU128.stk_of n _ 8 _ (by decide) $$ W8
    ihave B40 := FmtU128.stk_of n _ 1 _ (by decide) $$ B40
    iapply stk_addr (show (s - 48).toNat = s.toNat - 48 by omega)
    iapply frame_close n (s - 48).toNat
    iframe X0 X20 X28 X41 W8 B40
    isplitl [F8]; · iapply stk_word $$ F8
    isplitl [W24]; · iapply stk_word $$ W24
    isplitl [F24]; · iapply stk_word $$ F24
    iapply stk_word $$ F28
  iunfold argsAt, pieceArg
  iframe A0 A4 A8 A16 A20 P0 P4 G0 G4 Gt

theorem frame32_open (n a : Nat) :
    stk (GF := GF) n a 32 ⊢ stk n a 4 ∗ stk n (a + 4) 4 ∗ stk n (a + 8) 8 ∗ stk n (a + 16) 8 ∗
      stk n (a + 24) 8 := by
  iintro H
  icases stk_split n a 4 28 $$ H with ⟨H0, H⟩
  icases stk_split n (a + 4) 4 24 $$ H with ⟨H1, H⟩
  icases stk_split n (a + 4 + 4) 8 16 $$ H with ⟨H2, H⟩
  icases stk_split n (a + 4 + 4 + 8) 8 8 $$ H with ⟨H3, H4⟩
  rw [show a + 4 + 4 = a + 8 by omega, show a + 8 + 8 = a + 16 by omega,
    show a + 16 + 8 = a + 24 by omega]
  iframe H0 H1 H2 H3 H4

theorem frame32_close (n a : Nat) :
    stk (GF := GF) n a 4 ∗ stk n (a + 4) 4 ∗ stk n (a + 8) 8 ∗ stk n (a + 16) 8 ∗
      stk n (a + 24) 8 ⊢ stk n a 32 := by
  iintro ⟨H0, H1, H2, H3, H4⟩
  ihave H := stk_join n (a + 16) 8 8 $$ [H3 H4]
  · iframe H3; iexact H4
  ihave H := stk_join n (a + 8) 8 16 $$ [H2 H]
  · iframe H2; iexact H
  ihave H := stk_join n (a + 4) 4 24 $$ [H1 H]
  · iframe H1; iexact H
  iapply stk_join n a 4 28
  iframe H0 H

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Write::write_fmt(vec, ap)`** (746): the `Arguments` at `ap` copied to `sp + 8`
(`sp = s - 32`), `vec` stored at `sp + 4`, then `core::fmt::write(sp + 4, 1065404, sp + 8)`,
whose specification (`S872`) is a premise; its result returned. -/
theorem f746_gen (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s vec ap pp argp : UInt32) (junk : List UInt8) (hjunk : junk.length = 4) (hs : 32 ≤ s.toNat)
    (hap : ap.toNat + 24 ≤ 2 ^ 32) (P Q : IProp GF) (K : Nat) :
    inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
      MFunSpec cfg lim (d + 1) types[15]! inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 (s - 32 + 4), .i32 1065404, .i32 (s - 32 + 8)]⌝ ∗
          g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ argsAt n (s - 32 + 8) pp argp ∗
          n ↦[i32][ (s - 32 + 4).toNat ] vec ∗ P))
        (fun _ => K)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ argsAt n (s - 32 + 8) pp argp ∗
          n ↦[i32][ (s - 32 + 4).toNat ] vec ∗ Q))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f746 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 ap]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 32) 32 ∗ argsAt n ap pp argp ∗ n ↦[wms][ ap.toNat + 12 ] junk ∗ P))
        (fun _ => 60 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) + K)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 32) 32 ∗ argsAt n ap pp argp ∗ n ↦[wms][ ap.toNat + 12 ] junk ∗ Q)) := by
  iintro ⟨#Hi, #H872, #S872⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha872 := hm.funcs 872 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have hsp : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlt := s.toNat_lt
  have h4 : (s - 32 + 4).toNat = (s - 32).toNat + 4 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have h8 : (s - 32 + 8).toNat = (s - 32).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HA, HJ, HP⟩
  subst hargs
  iunfold argsAt at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  ihave Hs := stk_addr (show s.toNat - 32 = (s - 32).toNat by omega) $$ Hs
  icases frame32_open n (s - 32).toNat $$ Hs with ⟨X0, S4, S8, S16, S24⟩
  iunfold stk at S4 S8 S16 S24
  icases S4 with ⟨%w4, %hw4, S4⟩
  icases S8 with ⟨%w8, %hw8, S8⟩
  icases S16 with ⟨%w16, %hw16, S16⟩
  icases S24 with ⟨%w24, %hw24, S24⟩
  ihave L16 := (memBytes_append (GF := GF) (H := NearState) n (ap.toNat + 16) (bytes32 argp) (bytes32 1)).2 $$ [A16 A20]
  · iframe A16; iapply memBytes_addr (show ap.toNat + 20 = ap.toNat + 16 + (bytes32 argp).length by simp [bytes32]) $$ A20
  ihave L8 := (memBytes_append (GF := GF) (H := NearState) n (ap.toNat + 8) (bytes32 0) junk).2 $$ [A8 HJ]
  · iframe A8; iapply memBytes_addr (show ap.toNat + 12 = ap.toNat + 8 + (bytes32 0).length by simp [bytes32]) $$ HJ
  ihave L0 := (memBytes_append (GF := GF) (H := NearState) n ap.toNat (bytes32 pp) (bytes32 1)).2 $$ [A0 A4]
  · iframe A0; iapply memBytes_addr (show ap.toNat + 4 = ap.toNat + (bytes32 pp).length by simp [bytes32]) $$ A4
  simp only [f746]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [S4]
  repeat mstep
  mstep [L16]
  mstep [S24]
  repeat mstep
  mstep [L8]
  mstep [S16]
  repeat mstep
  mstep [L0]
  mstep [S8]
  repeat mstep
  have hb32 : ∀ v : UInt32, (bytes32 v).length = 4 := fun v => by simp [bytes32]
  rw [ResultExpect.bytes64_decode _ (by simp [hb32]), ResultExpect.bytes64_decode _ (by simp [hb32, hjunk]),
    ResultExpect.bytes64_decode _ (by simp [hb32])]
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 32).toNat + 8) (bytes32 pp) (bytes32 1)).1 $$ S8
    with ⟨B0, B4⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 32).toNat + 16) (bytes32 0) junk).1 $$ S16
    with ⟨B8, BJ⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 32).toNat + 24) (bytes32 argp) (bytes32 1)).1 $$ S24
    with ⟨B16, B20⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ap.toNat (bytes32 pp) (bytes32 1)).1 $$ L0
    with ⟨A0, A4⟩
  icases (memBytes_append (GF := GF) (H := NearState) n (ap.toNat + 8) (bytes32 0) junk).1 $$ L8
    with ⟨A8, AJ⟩
  icases (memBytes_append (GF := GF) (H := NearState) n (ap.toNat + 16) (bytes32 argp) (bytes32 1)).1 $$ L16
    with ⟨A16, A20⟩
  simp only [hb32]
  mcall S872 using [Hg S4 B0 B4 B8 B16 B20 HP]
  · iframe Hg HP
    isplitr [S4]
    · iunfold argsAt
      isplitl [B0]; · iapply memBytes_addr (show (s - 32).toNat + 8 = (s - 32 + 8).toNat by omega) $$ B0
      isplitl [B4]; · iapply memBytes_addr (show (s - 32).toNat + 8 + 4 = (s - 32 + 8).toNat + 4 by omega) $$ B4
      isplitl [B8]; · iapply memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 8).toNat + 8 by omega) $$ B8
      isplitl [B16]; · iapply memBytes_addr (show (s - 32).toNat + 24 = (s - 32 + 8).toNat + 16 by omega) $$ B16
      iapply memBytes_addr (show (s - 32).toNat + 24 + 4 = (s - 32 + 8).toNat + 20 by omega) $$ B20
    iapply memBytes_addr (show (s - 32).toNat + 4 = (s - 32 + 4).toNat by omega) $$ S4
  icases HQ with ⟨%hrs, Hg, HA, S4, HQ⟩
  subst hrs
  repeat mstep
  rw [show s - 32 + 32 = s by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  iunfold argsAt at HA
  icases HA with ⟨B0, B4, B8, B16, B20⟩
  iframe Hc Hg HQ
  isplitr; · ipureintro; rw [htype]; rfl
  isplitl [X0 S4 B0 B4 B8 BJ B16 B20]
  · iapply stk_addr (show (s - 32).toNat = s.toNat - 32 by omega)
    iapply frame32_close n (s - 32).toNat
    iframe X0
    isplitl [S4]
    · iapply stk_word
      iapply memBytes_addr (show (s - 32 + 4).toNat = (s - 32).toNat + 4 by omega) $$ S4
    isplitl [B0 B4]
    · iapply FmtU128.stk_of n _ 8 (bytes32 pp ++ bytes32 1) (by simp [hb32])
      iapply (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 pp) (bytes32 1)).2
      simp only [hb32]
      isplitl [B0]; · iapply memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by omega) $$ B0
      iapply memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 8 + 4 by omega) $$ B4
    isplitl [B8 BJ]
    · iapply FmtU128.stk_of n _ 8 (bytes32 0 ++ junk) (by simp [hb32, hjunk])
      iapply (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 0) junk).2
      simp only [hb32]
      iframe BJ
      iapply memBytes_addr (show (s - 32 + 8).toNat + 8 = (s - 32).toNat + 16 by omega) $$ B8
    iapply FmtU128.stk_of n _ 8 (bytes32 argp ++ bytes32 1) (by simp [hb32])
    iapply (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 argp) (bytes32 1)).2
    simp only [hb32]
    isplitl [B16]; · iapply memBytes_addr (show (s - 32 + 8).toNat + 16 = (s - 32).toNat + 24 by omega) $$ B16
    iapply memBytes_addr (show (s - 32 + 8).toNat + 20 = (s - 32).toNat + 24 + 4 by omega) $$ B20
  iunfold argsAt
  isplitl [A0 A4 A8 A16 A20]
  · iframe A0 A4 A8 A16; iapply memBytes_addr (show ap.toNat + 16 + 4 = ap.toNat + 20 by omega) $$ A20
  iapply memBytes_addr (show ap.toNat + 8 + 4 = ap.toNat + 12 by omega) $$ AJ

end Spec

end WNear.Binary.FmtWrite
