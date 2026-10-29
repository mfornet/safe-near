import Bridge.Functions.FmtWriteT

/-!
# `core::fmt::write` (872) on one piece and no argument

`core::panicking::panic(m, l, loc)` (853) builds `Arguments { pieces: [(m, l)], fmt: None, args: [] }`.
872 on it: `n = min(pieces.len, args.len) = 0`, so the loop is skipped (`br_if` to `@4`, `n := 0`),
and since `pieces.len = 1 > 0` it writes the trailing piece `pieces[0]` through the sink's
`write_str` (`call_indirect type 15`), then returns `Ok` (0).

`f872_p1`: from the sink's state `St0` to `St1` (`hSa`, the sink's `write_str` on the piece), at
`costP` (the prologue, the write and the epilogue).
-/

namespace WNear.Binary.FmtWriteP

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtWrite (act3 i64_fmt_init frame_open frame_close)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.FmtWriteT (argsT)
open WNear.Binary.FmtGrow (mwpi_select')

/-- The cost of 872 on one piece and no argument. -/
def costP (cfg : WasmConfig) (codeA : Func) (Ka : Nat) : Nat :=
  100 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) + Ka

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`core::fmt::write(data, vtab, ar)`** (872) on `Arguments { pieces: [(ptr0, len0)] at pp,
fmt: None, args: [] }`: the sink's `write_str` on the piece. -/
theorem f872_p1 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s data vtab ar pp argp idx ptr0 len0 : UInt32) (hs : 48 ≤ s.toNat) (har : ar.toNat + 24 ≤ 2 ^ 32)
    (hpp : pp.toNat + 8 ≤ 2 ^ 32) (a : Nat) (codeA : Func)
    (C : IProp GF) [Persistent C] (St0 St1 : IProp GF) (Ka : Nat)
    (hCa : C ⊢ inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst codeA)
    (hSa : C ⊢ MFunSpec cfg lim (d + 1) types[15]! inst mi codeA Cg
      (fun args => iprop(⌜args = [.i32 data, .i32 ptr0, .i32 len0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ St0))
      (fun _ => Ka) (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ St1))) :
    C ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f872 Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 vtab, .i32 ar]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsT n ar pp argp 1 0 ∗
          (n ↦[i32][ pp.toNat ] ptr0 ∗ n ↦[i32][ pp.toNat + 4 ] len0) ∗
          n ↦[i32][ vtab.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗ St0))
        (fun _ => costP cfg codeA Ka)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ argsT n ar pp argp 1 0 ∗
          (n ↦[i32][ pp.toNat ] ptr0 ∗ n ↦[i32][ pp.toNat + 4 ] len0) ∗
          n ↦[i32][ vtab.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗ St1)) := by
  iintro #C
  ihave ⟨#Hi, #Ha⟩ := hCa $$ C
  ihave #Sa := hSa $$ C
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hty15 : types[15]! = mi.types[15]! := by rw [hm.types]
  have hsp : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hlt := s.toNat_lt
  have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat 0) (UInt32.ofNat 1)) = 0 then
      Value.i32 (UInt32.ofNat 0) else Value.i32 (UInt32.ofNat 1)) = Value.i32 0 := by decide
  simp only [costP]
  generalize hACa : activationGas cfg.regularOpCost (entryLocals codeA [.i32 0, .i32 0, .i32 0]) = ACa
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HA, ⟨P0, P4⟩, V12, Ht, HS0⟩
  subst hargs
  iunfold argsT at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
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
  repeat mstep
  mstep [W32]
  repeat mstep
  have hx8 : (pp + (0 : UInt32) <<< (3 % 32)).toNat = pp.toNat := by simp
  generalize pp + (0 : UInt32) <<< (3 % 32) = x8 at hx8 ⊢
  mstep [P0] with exact (Nat.add_zero _).trans hx8
  mstep
  mstep [P4] with exact (by omega : x8.toNat + 4 = pp.toNat + 4)
  repeat mstep
  mstep [W36]
  mstep [V12]
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 ptr0, Value.i32 len0, Value.i32 idx] =
    [Value.i32 data, Value.i32 ptr0, Value.i32 len0] ++ [Value.i32 idx] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 20 * cfg.regularOpCost + R) 15 0 ta idx a types[15]!
    inst mi codeA [.i32 data, .i32 ptr0, .i32 len0] _ (fun _ => Ka) _ hta hty15 rfl (by omega)
  rw [act3, hACa]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Ht]; · iexact Ht
  isplitr; · iexact Ha
  isplitr; · iexact Hi
  isplitr; · iexact Sa
  isplitl [HS0 Hg]
  · isplitr; · ipureintro; rfl
    iframe Hg; iexact HS0
  inext
  iintro %rs Ht Hc HQ
  icases HQ with ⟨%hrs, Hg, HS⟩
  subst hrs
  mstep_post
  repeat mstep
  rw [show s - 48 + 48 = s by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  iframe Hc Hg V12 Ht HS
  isplitr; · ipureintro; rw [htype]; rfl
  isplitl [X0 X20 X28 W8 B40 X41 W16 W24 W32 W36]
  · iapply stk_addr (show (s - 48).toNat = s.toNat - 48 by omega)
    iapply frame_close n (s - 48).toNat
    iframe X0 X20 X28 X41
    isplitl [W8]; · iapply FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ W8
    isplitl [W16]; · iapply stk_word $$ W16
    isplitl [W24]; · iapply stk_word $$ W24
    isplitl [W32]; · iapply stk_word $$ W32
    isplitl [W36]; · iapply stk_word $$ W36
    iapply FmtU128.stk_of n _ 1 _ (by rfl) $$ B40
  isplitl [A0 A4 A8 A16 A20]
  · iunfold argsT; iframe A0 A4 A8 A16 A20
  iframe P0 P4

end Spec

end WNear.Binary.FmtWriteP
