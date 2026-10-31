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
/-- Actual serde Debug prefix constructs its String/Arguments and calls String::write_fmt.
The selected ErrorCode formatter remains an explicit operational dependency. -/
theorem f641_first_format_exists (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp desc fmt e x2 : UInt32) (x3 : UInt64)
    (S : Nat) (hsp : S + 80 ≤ sp.toNat) (hdesc : desc.toNat + 4 ≤ 2 ^ 32)
    (P : IProp GF) (Q : UInt32 → UInt32 → UInt32 → IProp GF) (K : Nat) (Φ : Post NearState GF) :
    inst ↪[inst] mi ∗ A 598 ↪[wf] FuncInst.wasm types[13]! inst f598 ∗
      ErrorCodeStringWriteSpec cfg lim (d + 1) inst mi n g gt sp e S K Cg P Q ∗
      credits Cg (100 * cfg.regularOpCost + K + R) ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      stk n (sp.toNat - (S + 80)) (S + 80) ∗ n ↦[i32][ desc.toNat ] e ∗ P ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, ∀ l : UInt32, credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (sp - 80)⟩ ∗ stk n ((sp - 80).toNat - S) S ∗
        stk n (sp - 80).toNat 16 ∗ stk n ((sp - 80).toNat + 24) 16 ∗
        stringCells n (sp - 80 + 40) p c l ∗ firstErrorArg n (sp - 80) e ∗
        (∃ pad : UInt32, firstErrorArgs n (sp - 80) pad) ∗ n ↦[i32][ desc.toNat ] e ∗ Q p c l -∗
        Φ.normal [.i32 0] (debugFrame inst mi e fmt (sp - 80) x3)) ⊢
      mwpi cfg lim d (debugFrame inst mi desc fmt x2 x3) [] (f641.body.take 49) Φ := by
  unfold ErrorCodeStringWriteSpec
  iintro ⟨#Hi, #F598, #S598, Hc, Hg, Hs, Desc, HP, HΦ⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha598 := hm.funcs 598 (by decide)
  have t13 : types[13]!.params.length = 2 := rfl
  have hlt := sp.toNat_lt
  have h80 : (sp - 80).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h40 : (sp - 80 + 40).toNat = (sp - 80).toNat + 40 := by simp [UInt32.toNat_add]; omega
  have h56 : (sp - 80 + 56).toNat = (sp - 80).toNat + 56 := by simp [UInt32.toNat_add]; omega
  icases stk_split n _ S 80 $$ Hs with ⟨Low, Hs⟩
  ihave Low := stk_addr (show sp.toNat - (S + 80) = (sp - 80).toNat - S by omega) $$ Low
  ihave Hs := stk_addr (show sp.toNat - (S + 80) + S = (sp - 80).toNat by omega) $$ Hs
  icases stk_split n _ 16 64 $$ Hs with ⟨Pad0, Hs⟩
  icases stk_split n _ 8 56 $$ Hs with ⟨A16, Hs⟩
  icases stk_split n _ 16 40 $$ Hs with ⟨Pad24, Hs⟩
  icases stk_split n _ 16 24 $$ Hs with ⟨A40, Hs⟩
  icases stk_split n _ 16 8 $$ Hs with ⟨A56, A72⟩
  icases stk_split n _ 4 4 $$ A16 with ⟨W16, W20⟩
  icases VecFromElem.stk16 n _ $$ A40 with ⟨W40, W44, W48, W52⟩
  icases VecFromElem.stk16 n _ $$ A56 with ⟨W56, W60, W64, W68⟩
  icases stk_split n _ 4 4 $$ A72 with ⟨W72, W76⟩
  icases stk4_word n _ $$ W16 with ⟨%v16, W16⟩
  icases stk4_word n _ $$ W20 with ⟨%v20, W20⟩
  icases stk4_word n _ $$ W40 with ⟨%v40, W40⟩
  icases stk4_word n _ $$ W44 with ⟨%v44, W44⟩
  icases stk4_word n _ $$ W48 with ⟨%v48, W48⟩
  icases stk4_word n _ $$ W52 with ⟨%v52, W52⟩
  icases stk4_word n _ $$ W56 with ⟨%v56, W56⟩
  icases stk4_word n _ $$ W60 with ⟨%v60, W60⟩
  icases stk4_word n _ $$ W64 with ⟨%v64, W64⟩
  icases stk4_word n _ $$ W68 with ⟨%v68, W68⟩
  icases stk4_word n _ $$ W72 with ⟨%v72, W72⟩
  icases stk4_word n _ $$ W76 with ⟨%v76, W76⟩
  simp only [Nat.add_assoc, Nat.reduceAdd]
  ihave W40 := BorshFT.join64' (n := n) (a := (sp - 80).toNat + 40) (b := (sp - 80).toNat + 44)
    v40 v44 (by omega) $$ [W40 W44]
  · iframe W40 W44
  ihave W60 := BorshFT.join64' (n := n) (a := (sp - 80).toNat + 60) (b := (sp - 80).toNat + 64)
    v60 v64 (by omega) $$ [W60 W64]
  · iframe W60 W64
  simp only [f641, List.take, debugFrame]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [W48]
  mstep; mstep; mstep [W40]
  mstep; mstep; mstep [Desc]; mstep; mstep [W52]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [W76]
  mstep; mstep; mstep [W60]
  mstep; mstep; mstep [W56]
  mstep; mstep; mstep [W20]
  mstep; mstep; mstep; mstep; mstep [W72]
  mstep; mstep; mstep; mstep; mstep [W16]
  mstep; mstep; mstep; mstep; mstep; mstep
  rw [show storeBytes (.i64 1) 8 = bytes32 1 ++ bytes32 0 by decide]
  icases (memBytes_append n ((sp - 80).toNat + 40) (bytes32 1) (bytes32 0)).1 $$ W40 with ⟨W40, W44⟩
  icases (memBytes_append n ((sp - 80).toNat + 60) (bytes32 1) (bytes32 0)).1 $$ W60 with ⟨W60, W64⟩
  simp only [bytes32_length, Nat.add_assoc, Nat.reduceAdd]
  ihave A0 := BorshFT.join64' (n := n) (a := (sp - 80).toNat + 56) (b := (sp - 80).toNat + 60)
    1057628 1 (by omega) $$ [W56 W60]
  · iframe W56 W60
  ihave A8 := BorshFT.join64' (n := n) (a := (sp - 80).toNat + 64) (b := (sp - 80).toNat + 68)
    0 v68 (by omega) $$ [W64 W68]
  · iframe W64 W68
  ihave A16 := BorshFT.join64' (n := n) (a := (sp - 80).toNat + 72) (b := (sp - 80).toNat + 76)
    (sp - 80 + 16) 1 (by omega) $$ [W72 W76]
  · iframe W72 W76
  ispecialize S598 $$ %v68
  mcall S598 using [Hg Low W40 W44 W48 W16 W20 W52 A0 A8 A16 HP] with (mstep_norm_full; omega)
  · iunfold stringCells, firstErrorArg, firstErrorArgs, args24
    simp only [h40, h56, Nat.add_assoc, Nat.reduceAdd, VecFromElem.storeBytes_pair64]
    iframe Hg Low W40 W44 W48 W16 W20 W52 A0 A8 A16 HP
  icases HQ with ⟨%hrs, Hg, Low, %p, %c, %l, HC, HE, HA, HQ⟩
  subst hrs
  mcredits R
  ispecialize HΦ $$ %p %c %l
  iapply HΦ $$ [Hc Hg Low Pad0 Pad24 HC HE HA Desc HQ]
  iframe Hc Hg Low Pad0 Pad24 HC HE Desc HQ
  iexists v68
  iexact HA

end WNear.Binary.SerdeDebug
