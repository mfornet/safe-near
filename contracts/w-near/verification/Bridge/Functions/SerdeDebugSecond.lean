import Bridge.Functions.SerdeDebugResources

namespace WNear.Binary.SerdeDebug
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr stk_intro stk_word)
open WNear.Binary.PanicHook (stk4_word)
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- Actual second-format setup after the checked successful first String writer.
The chosen Formatter writer remains explicit and preserves all cells needed for cleanup. -/
theorem f641_second_format (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s fmt e : UInt32) (x3 : UInt64)
    (S : Nat) (hS : S ≤ s.toNat) (hs : s.toNat + 80 ≤ 2 ^ 32)
    (p c l ret : UInt32) (P Q : IProp GF) (K : Nat) (Φ : Post NearState GF) :
    inst ↪[inst] mi ∗ A 610 ↪[wf] FuncInst.wasm types[0]! inst f610 ∗
      A 725 ↪[wf] FuncInst.wasm types[31]! inst f725 ∗ A 913 ↪[wf] FuncInst.wasm types[13]! inst f913 ∗
      ErrorEnvelopeWriteSpec cfg lim (d + 1) inst mi n g gt s fmt e p c l ret S K Cg P Q ∗
      credits Cg (200 * cfg.regularOpCost + K + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗
      stk n s.toNat 16 ∗ stk n (s.toNat + 24) 16 ∗ stringCells n (s + 40) p c l ∗
      firstErrorArg n s e ∗ (∃ pad : UInt32, firstErrorArgs n s pad) ∗ P ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗
        stk n s.toNat 16 ∗ stringCells n (s + 40) p c l ∗ n ↦[i32][ s.toNat + 52 ] e ∗
        (∃ pad : UInt32, secondErrorArgs n s pad) ∗ secondErrorValues n s e ∗ Q -∗
        Φ.normal [.i32 ret] (debugFrame inst mi e fmt s (VecFromElem.pair64 (e + 12) 3))) ⊢
      mwpi cfg lim d (debugFrame inst mi e fmt s x3) [.i32 0] ((f641.body.drop 49).take 56) Φ := by
  unfold ErrorEnvelopeWriteSpec
  iintro ⟨#Hi, #F610, #F725, #F913, #S913, Hc, Hg, Low, Pad0, Pad24, HC, HE, HA, HP, HΦ⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha610 := hm.funcs 610 (by decide)
  have ha725 := hm.funcs 725 (by decide)
  have ha913 := hm.funcs 913 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t31 : types[31]!.params.length = 3 := rfl
  have t13 : types[13]!.params.length = 2 := rfl
  have hlt := s.toNat_lt
  have h16 : (s + 16).toNat = s.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have h40 : (s + 40).toNat = s.toNat + 40 := by simp [UInt32.toNat_add]; omega
  have h56 : (s + 56).toNat = s.toNat + 56 := by simp [UInt32.toNat_add]; omega
  iunfold firstErrorArg at HE
  icases HE with ⟨W16, W20, W52⟩
  icases HA with ⟨%pad68, HA⟩
  iunfold firstErrorArgs, args24 at HA
  icases HA with ⟨A56, A64, A72⟩
  simp only [VecFromElem.storeBytes_pair64, h56, Nat.add_assoc, Nat.reduceAdd]
  icases BorshFT.split64' (n := n) (a := s.toNat + 56) (b := s.toNat + 60) 1057628 1 (by omega) $$ A56 with ⟨W56, W60⟩
  icases VecFromElem.stk16 n _ $$ Pad0 with ⟨W0, W4, W8, W12⟩
  icases VecFromElem.stk16 n _ $$ Pad24 with ⟨W24, W28, W32, W36⟩
  icases stk4_word n _ $$ W0 with ⟨%v0, W0⟩
  icases stk4_word n _ $$ W4 with ⟨%v4, W4⟩
  icases stk4_word n _ $$ W8 with ⟨%v8, W8⟩
  icases stk4_word n _ $$ W12 with ⟨%v12, W12⟩
  icases stk4_word n _ $$ W24 with ⟨%v24, W24⟩
  icases stk4_word n _ $$ W28 with ⟨%v28, W28⟩
  icases stk4_word n _ $$ W32 with ⟨%v32, W32⟩
  icases stk4_word n _ $$ W36 with ⟨%v36, W36⟩
  simp only [Nat.add_assoc, Nat.reduceAdd]
  simp only [f641, List.drop, List.take, debugFrame]
  mcall (FormatResult.f610_success cfg lim (d + 1) types[0]! rfl inst mi n g ta A hm Cg gt s) using [Hg]
    with (mstep_norm_full; omega)
  · iframe Hg
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (FormatResult.f725_pair cfg lim (d + 1) types[31]! rfl inst mi n hn Cg (s + 8) (e + 12) 3
    v8 v12 (by simp [UInt32.toNat_add]; omega)) using [W8 W12] with (mstep_norm_full; omega)
  · simp only [show (s + 8).toNat = s.toNat + 8 by simp [UInt32.toNat_add]; omega, Nat.add_assoc, Nat.reduceAdd]
    iframe W8 W12
  icases HQ with ⟨%hrs, W8, W12⟩
  subst hrs
  ihave Line := BorshFT.join64' (n := n) (a := (s + 8).toNat) (b := (s + 8).toNat + 4)
    (e + 12) 3 rfl $$ [W8 W12]
  · iframe W8 W12
  mstep; mstep [Line]; mstep
  rw [VecFromElem.ofNat_decode_pair]
  mstep; mstep; mstep; mstep; mstep
  mcall (FormatResult.f725_pair cfg lim (d + 1) types[31]! rfl inst mi n hn Cg s (e + 16) 3
    v0 v4 (by omega)) using [W0 W4] with (mstep_norm_full; omega)
  · iframe W0 W4
  icases HQ with ⟨%hrs, W0, W4⟩
  subst hrs
  ihave Col := BorshFT.join64' (n := n) (a := s.toNat) (b := s.toNat + 4) (e + 16) 3 rfl $$ [W0 W4]
  · iframe W0 W4
  ihave A20 := BorshFT.join64' (n := n) (a := s.toNat + 20) (b := s.toNat + 24) 126 v24 (by omega) $$ [W20 W24]
  · iframe W20 W24
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [W36]
  mstep; mstep; mstep [A64]
  mstep; mstep; mstep [W60]
  mstep; mstep; mstep [A20]
  mstep; mstep; mstep [W16]
  mstep; mstep; mstep [Col]; mstep [A72]
  rw [VecFromElem.ofNat_decode_pair]
  mstep; mstep; mstep; mstep; mstep [W56]
  mstep; mstep; mstep; mstep; mstep [W32]
  mstep; mstep; mstep; mstep
  rw [show storeBytes (.i64 4) 8 = bytes32 4 ++ bytes32 0 by decide]
  icases (memBytes_append n (s.toNat + 20) (bytes32 4) (bytes32 0)).1 $$ A20 with ⟨W20, W24⟩
  simp only [bytes32_length, Nat.add_assoc, Nat.reduceAdd]
  ihave A16 := BorshFT.join64' (n := n) (a := s.toNat + 16) (b := s.toNat + 20) 1061532 4 (by omega) $$ [W16 W20]
  · iframe W16 W20
  ihave A24 := BorshFT.join64' (n := n) (a := s.toNat + 24) (b := s.toNat + 28) 0 v28 (by omega) $$ [W24 W28]
  · iframe W24 W28
  ihave A32 := BorshFT.join64' (n := n) (a := s.toNat + 32) (b := s.toNat + 36) (s + 56) 3 (by omega) $$ [W32 W36]
  · iframe W32 W36
  ihave A56 := BorshFT.join64' (n := n) (a := s.toNat + 56) (b := s.toNat + 60) (s + 40) 127 (by omega) $$ [W56 W60]
  · iframe W56 W60
  ispecialize S913 $$ %v28
  mcall S913 using [Hg Low HC A16 A24 A32 A56 A64 A72 HP] with (mstep_norm_full; omega)
  · iunfold secondErrorArgs, secondErrorValues, args24
    simp only [h16, h56, Nat.add_assoc, Nat.reduceAdd, VecFromElem.storeBytes_pair64]
    iframe Hg Low HC A16 A24 A32 A56 A64 A72 HP
  icases HQ with ⟨%hrs, Hg, Low, HC, HA, HV, HQ⟩
  subst hrs
  ihave Line := stk_intro n ((s + 8).toNat) (bytes32 (e + 12) ++ bytes32 3) $$ Line
  ihave Col := stk_intro n s.toNat (bytes32 (e + 16) ++ bytes32 3) $$ Col
  simp only [List.length_append, bytes32_length, show (s + 8).toNat = s.toNat + 8 by simp [UInt32.toNat_add]; omega]
  ihave Pad0 := stk_join n s.toNat 8 8 $$ [Col Line]
  · iframe Col Line
  mcredits R
  iapply HΦ $$ [Hc Hg Low Pad0 HC W52 HA HV HQ]
  iframe Hc Hg Low Pad0 HC W52 HV HQ
  iexists v28
  iexact HA

end WNear.Binary.SerdeDebug
