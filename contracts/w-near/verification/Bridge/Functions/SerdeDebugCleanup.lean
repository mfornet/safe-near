import Bridge.Functions.SerdeDebugAdapters

namespace WNear.Binary.SerdeDebug
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr stk_intro stk_word)
open WNear.Binary.PanicHook (stk4_word)
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Actual serde Debug cleanup frees only its temporary String and restores the entire original frame. -/
theorem f641_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s fmt e ret : UInt32) (x3 : UInt64)
    (S : Nat) (hS : S ≤ s.toNat) (hs : s.toNat + 80 ≤ 2 ^ 32)
    (p c l : UInt32) (maxP len F : Nat) (live : List (Nat × Nat)) (Q : IProp GF) (Φ : Post NearState GF) :
    DropVec.dropCode inst mi A ∗ A 601 ↪[wf] FuncInst.wasm types[31]! inst f601 ∗
      A 599 ↪[wf] FuncInst.wasm types[0]! inst f599 ∗
      credits Cg (400 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗
      stk n s.toNat 16 ∗ stringCells n (s + 40) p c l ∗ n ↦[i32][ s.toNat + 52 ] e ∗
      (∃ pad : UInt32, secondErrorArgs n s pad) ∗ secondErrorValues n s e ∗
      AllocInv.heapInv n maxP len live F ∗
      (if c = 0 then emp else ⌜(p.toNat, c.toNat) ∈ live⌝ ∗ AllocInv.block n p.toNat c.toNat) ∗ Q ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 80)⟩ ∗ stk n (s.toNat - S) (S + 80) ∗
        AllocInv.heapInv n maxP len (if c = 0 then live else live.erase (p.toNat, c.toNat))
          (if c = 0 then F else F + 1) ∗ Q -∗
        Φ.normal [.i32 ret] (debugFrame inst mi ret fmt s x3)) ⊢
      mwpi cfg lim d (debugFrame inst mi e fmt s x3) [.i32 ret] (f641.body.drop 105) Φ := by
  iintro ⟨#HD, #F601, #F599, Hc, Hg, Low, Pad0, HC, W52, HA, HV, Hinv, Hb, Hdata, HΦ⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold DropVec.dropCode at HD
    icases HD with ⟨#Hi, -⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha599 := hm.funcs 599 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have hlt := s.toNat_lt
  have h16 : (s + 16).toNat = s.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have h40 : (s + 40).toNat = s.toNat + 40 := by simp [UInt32.toNat_add]; omega
  have h56 : (s + 56).toNat = s.toNat + 56 := by simp [UInt32.toNat_add]; omega
  iunfold stringCells at HC
  icases HC with ⟨Ptr, Cap, Len⟩
  simp only [f641, List.drop, debugFrame]
  mstep; mstep; mstep; mstep
  mcall (f599_drop cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP len live F
    (s + 40) p c (by simp [UInt32.toNat_add]; omega)) using [Ptr Cap Hinv Hb] with (mstep_norm_full; omega)
  · iframe Ptr Cap Hinv Hb
  icases HQ with ⟨%hrs, Ptr, Cap, Hinv⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]; mstep
  ihave HC : stringCells n (s + 40) p c l $$ [Ptr Cap Len]
  · iunfold stringCells
    iframe Ptr Cap Len
  ihave HC := stringCells_stack n (s + 40) p c l $$ HC
  ihave W52 := stk_word n (s.toNat + 52) e $$ W52
  icases HA with ⟨%pad, HA⟩
  iunfold secondErrorArgs at HA
  ihave HA := args24_stack n (s + 16) (VecFromElem.pair64 1061532 4) (VecFromElem.pair64 0 pad)
    (VecFromElem.pair64 (s + 56) 3) $$ HA
  iunfold secondErrorValues at HV
  ihave HV := args24_stack n (s + 56) (VecFromElem.pair64 (s + 40) 127) (VecFromElem.pair64 (e + 12) 3)
    (VecFromElem.pair64 (e + 16) 3) $$ HV
  simp only [h16, h40, h56]
  ihave H40 := stk_join n (s.toNat + 40) 12 4 $$ [HC W52]
  · simp only [Nat.add_assoc, Nat.reduceAdd]; iframe HC W52
  ihave H0 := stk_join n s.toNat 16 24 $$ [Pad0 HA]
  · iframe Pad0 HA
  ihave H0 := stk_join n s.toNat 40 16 $$ [H0 H40]
  · iframe H0 H40
  ihave H0 := stk_join n s.toNat 56 24 $$ [H0 HV]
  · iframe H0 HV
  ihave H0 := stk_addr (show s.toNat = (s.toNat - S) + S by omega) $$ H0
  ihave Hs := stk_join n (s.toNat - S) S 80 $$ [Low H0]
  · iframe Low H0
  mcredits R
  iapply HΦ $$ [Hc Hg Hs Hinv Hdata]
  iframe Hc Hg Hs Hinv Hdata

end WNear.Binary.SerdeDebug
