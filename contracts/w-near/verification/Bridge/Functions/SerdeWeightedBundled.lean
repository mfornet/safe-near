import Bridge.Functions.SerdeIgnWeightedReader
import Bridge.Functions.SerdeBundledSelected

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeStructObjPhaseReaders

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (strRun borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (scratchPre)

open WNear.Binary.SerdeStructObjKeyState (Bounds core key_exact scratch_alignment)
open WNear.Binary.SerdeStructObjPhase (Phase)


section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.SerdeIgnExecution
/-- The remaining obligations concern only physically reachable scratch states. Room and final capacity are derived. -/
def WeightedIgnoreConditions (cfg : WasmConfig) (bs : List UInt8) (K : Nat → Nat) (B : PhaseBounds) : Prop :=
  ∀ key i hl F cap r ops, key ≠ "account_id" → B (.value key) i hl F cap → cap.toNat < 2 ^ 25 → i ≤ bs.length →
    bs[i + wsLen (bs.drop i)]? = some 0x3A →
    SerdeIgnMachineTrace.trace (bs.drop (i + wsLen (bs.drop i) + 1)) = some (r, ops) →
    hl % 65536 = 0 → 0 < hl →
    hl ≤ 100663296 ∧
    (166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1)) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap 0 ops ≤ K (i + wsLen (bs.drop i) + 1) ∧
    ∀ hl', HeapTrace hl cap 0 ops hl' →
      B (.member false) (bs.length - r.length) hl' (SerdeIgnTrace.endFreeBound F cap 0 ops) (SerdeIgnTrace.endState cap 0 ops).1


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ignoreHyp_weighted_v86 (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : PhaseBounds) (K : Nat → Nat)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hconditions : WeightedIgnoreConditions cfg bs K B) (hconditionsSaved : WeightedIgnoreConditions cfg bs K Bsaved)
    (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeEnds.endCode n 2048 inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code n 2048 inst mi A) :
    SerdeStructObjPhase.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs SerdeIgnObject.ignored K
      (member n 2048 ta (A 578) idx de live B Bsaved) Cd := by
  intro d s i rest seen key hkey hd hsp hsend hi hcolon hmodel
  unfold SerdeIgnObject.ignored at hmodel
  simp only [Option.map_eq_some_iff] at hmodel
  obtain ⟨r', hskip, he⟩ := hmodel
  cases he
  obtain ⟨ops, htrace, _, _, _, _⟩ := SerdeIgnMachineTrace.trace_some hskip
  have hs32 : (s + 32).toNat = s.toNat + 32 := by simp [UInt32.toNat_add]; omega
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  iintro #HCd
  ihave Hcode := hcode $$ HCd
  icases Hcode with ⟨#Hend, #F89, #F81, #HC⟩
  iunfold MFunSpec
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, M32, Hg, H304, Hrd, Hseen⟩
  icases seen_core n 2048 ta (A 578) idx de s live B Bsaved (.value key) i seen $$ Hseen with
    ⟨%C, %lv, %hC, Hcore, Hsaved⟩
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %p, %cap, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  have hcond : WeightedIgnoreConditions cfg bs K C := by
    rcases hC with rfl | rfl
    · exact hconditions
    · exact hconditionsSaved
  icases SerdeStructObjKeyState.scratch_alignment n 2048 hl lv F de p cap sl $$ Hscratch with
    ⟨%⟨halign, hpositive⟩, Hscratch⟩
  obtain ⟨hceiling, hgas, hbound⟩ := hcond key i hl F cap rest ops hkey hb hcap hi hcolon htrace halign hpositive
  have hendcap := trace_end_cap_v86 (bs.drop (i + wsLen (bs.drop i) + 1)) rest ops cap
    (by simp only [List.length_drop]; omega) hcap htrace
  iunfold SerdeValueState.tables at Htables
  icases Htables with ⟨Hesc, Hwidth, Hhex⟩
  have callIgnore := (f201_weighted_v86 (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt s (s + 32) de ptr p cap sl idx
    hl F lv bs rest ops i
    (iprop(n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
    (by omega) hde (by rw [hs32]; omega) hlen hptr hi hcolon (by omega) htrace hpositive halign hceiling).trans
      (AllocGen.MFunSpec_cost (K' := fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + K (i + wsLen (bs.drop i) + 1))
        (fun _ => by omega))
  rw [hs32] at callIgnore
  ihave #S := callIgnore $$ [Hend F89 F81 HC]
  · iframe Hend F89 F81 HC
  clear callIgnore
  iunfold MFunSpec at S
  icases VecFromElem.stk_split n (s.toNat - 304) 144 160 $$ H304 with ⟨H144, H160⟩
  rw [show s.toNat - 304 + 144 = s.toNat - 160 by omega]
  iapply mwpInvoke_wand
  isplitl [M32 Hg H160 Hvt Hscratch Hrd Hesc Hhex Hident Hwidth Hkey Hc]
  · iapply S $$ %args %R [M32 Hg H160 Hvt Hscratch Hrd Hesc Hhex Hident Hwidth Hkey] Hc
    dsimp only
    iframe M32 Hg H160 Hvt Hscratch Hrd Hesc Hhex Hident Hwidth Hkey
    ipureintro; exact ha
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %p', %hl', %⟨hrs, hheap⟩, M32, Hg, H160, Hvt, Hst, Hrd, Hesc, Hhex, Hident, Hwidth, Hkey⟩
    have hb' := hbound hl' hheap
    iframe Hc M32 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H144 H160]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 144 160
      rw [show s.toNat - 304 + 144 = s.toNat - 160 by omega]
      iframe H144 H160
    iapply Hsaved $$ %(.member false) %(bs.length - rest.length)
    iunfold core
    iexists hl', SerdeIgnTrace.endFreeBound F cap 0 ops, p', (SerdeIgnTrace.endState cap 0 ops).1, 0
    iframe Hvt Hkey Hident
    isplitr
    · ipureintro; exact ⟨hb', hendcap⟩
    isplitl [Hesc Hwidth Hhex]
    · iunfold SerdeValueState.tables
      iframe Hesc Hwidth Hhex
    iunfold SerdeIgnStack.state at Hst
    icases Hst with ⟨D0, D4, D8, Hsb⟩
    iunfold SerdeValueState.scratchPre
    rw [hd12]
    simp only [List.length_nil, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
    iframe D8 D0 D4 Hsb
  · iintro Htrap; iexact Htrap

end Resource
end WNear.Binary.SerdeStructObjPhaseReaders

namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeRead (wsLen)
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeStructObjPhaseReaders (PhaseBounds)

/-- Actual prefix history constrains the concrete scratch coordinates at each phase. -/
def WeightedIgnoreGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ key i hl F cap rest ops, key ≠ "account_id" → B (.value key) i hl F cap →
    cap.toNat < 2 ^ 25 → i ≤ bs.length → bs[i + wsLen (bs.drop i)]? = some 0x3A →
    SerdeIgnMachineTrace.trace (bs.drop (i + wsLen (bs.drop i) + 1)) = some (rest, ops) →
    hl % 65536 = 0 → 0 < hl →
    (166 + 470 * (bs.length - rest.length - (i + wsLen (bs.drop i) + 1)) - 74 * SerdeIgnTrace.pushCount ops) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap 0 ops ≤ K (i + wsLen (bs.drop i) + 1)

theorem Bound.weighted_ignore_conditions (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) (K : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hbase : baseHL + 18230154 ≤ 100663296)
    (hgas : WeightedIgnoreGasCharges cfg bs (Bound bs start baseHL baseF saved) K) :
    SerdeStructObjPhaseReaders.WeightedIgnoreConditions cfg bs K (Bound bs start baseHL baseF saved) := by
  intro key i hl F cap rest ops hkey hb hc hi hcolon ht hal hp
  refine ⟨Ledger.heap_ceiling bs baseHL baseF i hl F saved cap hlen hbase hb.forget,
    hgas key i hl F cap rest ops hkey hb hc hi hcolon ht hal hp, ?_⟩
  intro hl' hh
  have hskip : WNear.IgnoreModel.vSkip (bs.drop (i + wsLen (bs.drop i) + 1)) = some rest := by
    rw [← SerdeIgnMachineTrace.erase_trace, ht]
    rfl
  have hr := JsonSuffix.drop_suf' (IgnoreShallow.vSkip_suf hskip)
  have hrlen := WNear.IgnoreModel.vSkip_length hskip
  simp only [List.length_drop] at hrlen
  have hvle := SerdeNextKey.getElem_lt hcolon
  have hheap := SerdeIgnExecution.heap_pages_bound hl cap 0 ops hl' hh
  apply Bound.segment bs start baseHL baseF i (bs.length - rest.length) hl F hl' saved saved
    (.value key) (.member false) cap (.frames ops) 0 (by omega)
  · intro pre hpre
    have hv : ValueSegment bs key (bs.drop (i + wsLen (bs.drop i) + 1))
        (bs.length - rest.length) (.frames ops) :=
      .ignored _ ops hkey rfl (by simpa only [hr] using ht)
    have hdup : key = "account_id" → saved = false := fun heq => False.elim (hkey heq)
    have hres := Prefix.value hpre hdup hcolon (by omega) (by omega) hv
    have hkfalse : (key == "account_id") = false := by simp [hkey]
    simpa only [hkfalse, Bool.or_false] using hres
  · exact hb
  · exact hheap.1
  · simpa only [Segment.pages, Nat.add_zero, Nat.mul_comm] using hheap.2.1


end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeRead (wsLen)
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeStructObjPhaseReaders (PhaseBounds)

/-- Actual prefix history constrains the concrete scratch coordinates at each phase. -/
noncomputable def selectedWeightedIgnoreCost (cfg : WasmConfig) (bs : List UInt8) (start baseF v : Nat) : Nat := by
  classical
  exact if h : Nonempty (IgnoreWitness bs start v) then
    let w := Classical.choice h
    (166 + 470 * (bs.length - w.rest.length - v) - 74 * SerdeIgnTrace.pushCount w.ops) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history) 0 w.ops
  else 0

theorem selectedWeightedIgnoreCost_of_witness (cfg : WasmConfig) (bs : List UInt8) (start baseF v : Nat)
    (w : IgnoreWitness bs start v) :
    (166 + 470 * (bs.length - w.rest.length - v) - 74 * SerdeIgnTrace.pushCount w.ops) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history) 0 w.ops =
      selectedWeightedIgnoreCost cfg bs start baseF v := by
  classical
  unfold selectedWeightedIgnoreCost
  rw [dif_pos ⟨w⟩]
  let other := Classical.choice (show Nonempty (IgnoreWitness bs start v) from ⟨w⟩)
  change _ = (166 + 470 * (bs.length - other.rest.length - v) - 74 * SerdeIgnTrace.pushCount other.ops) * cfg.regularOpCost +
    SerdeIgnTrace.extraCost cfg (endFreeBound baseF 0 other.history) (endCap 0 other.history) 0 other.ops
  have hhistory := w.history_unique other
  have hmodel := Option.some.inj (w.model.symm.trans other.model)
  have hr := congrArg Prod.fst hmodel
  have ho := congrArg Prod.snd hmodel
  dsimp only at hr ho
  rw [hhistory, hr, ho]

theorem Bound.selected_weighted_ignore_charges (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) : WeightedIgnoreGasCharges cfg bs (Bound bs start baseHL baseF saved)
      (selectedWeightedIgnoreCost cfg bs start baseF) := by
  intro key i hl F cap rest ops hkey hb hc hi hcolon ht hal hp
  obtain ⟨pre, hprefix, hcap, hfree, hlo, hhi⟩ := hb
  subst cap F
  exact Nat.le_of_eq (selectedWeightedIgnoreCost_of_witness cfg bs start baseF (i + wsLen (bs.drop i) + 1)
    ⟨key, i, saved, rest, ops, pre, hprefix, hkey, hcolon, rfl, ht⟩)


end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.SerdeStructObjPhaseReaders
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (strRun borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (scratchPre)

open WNear.Binary.SerdeStructObjKeyState (Bounds core key_exact scratch_alignment)
open WNear.Binary.SerdeStructObjPhase (Phase)

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeStructObjModelState (code code_keys code_values)
open WNear.Binary.SerdeIgnObject (ignored ignored_agrees)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000
set_option maxRecDepth 100000 in
theorem object_loop_v86_closing_bundled_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : PhaseBounds) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : BundledKeyConditions cfg 2048 bs B K646) (hkeysSaved : BundledKeyConditions cfg 2048 bs Bsaved K646)
    (hvalues : ValueConditions cfg 2048 bs B Bsaved K169)
    (hclose : ClosingConditions bs B)
    (hcloseSaved : ClosingConditions bs Bsaved)
    (hignored : WeightedIgnoreConditions cfg bs K81 B)
    (hignoredSaved : WeightedIgnoreConditions cfg bs K81 Bsaved)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live B Bsaved (.member true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live B Bsaved .done (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hcode : iprop(SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd)) ⊢
      SerdeEnds.endCode n 2048 inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
        A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code n 2048 inst mi A := by
    iintro ⟨#Hobj, #Hmember, _⟩
    iunfold SerdeStructObjModelState.code at Hobj
    icases Hobj with ⟨#C193, -, -, -, -, -, #F89, -, #F81, -⟩
    iunfold SerdeNextKey.code193 at C193
    icases C193 with ⟨#Cend, -⟩
    iframe Cend F89 F81 Hmember
  have hignore := ignoreHyp_weighted_v86 cfg lim inst mi A n g ta Cg hm gt idx de ptr bs live B Bsaved K81 hlen hptr (by omega)
    hignored hignoredSaved iprop(SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd)) hcode
  exact f228_obj_model_closing_bundled cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx x2 x3 x4 x5
    ob bs i 2048 live iprop(SerdeIgnMember.code n 2048 inst mi A ∗ Cd) B Bsaved K646 K169 K81 ignored ignored_agrees
    hob hout (by omega) hptr hde hsp hal hi hkeys hkeysSaved hvalues hclose hcloseSaved hignore N a rF hb0 hloop
end Resource
end WNear.Binary.SerdeStructObjPhaseReaders
namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeRead (wsLen)
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeStructObjPhaseReaders (PhaseBounds)


open WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.SerdeStructModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjPhaseReaders (member)
open WNear.Binary.SerdeIgnObject (ignored)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem object_loop_bundled_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K646) (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K169)
    (hignored : WeightedIgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K81) (hignoredSaved : WeightedIgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K81)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) (.member true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) .done (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  exact SerdeStructObjPhaseReaders.object_loop_v86_closing_bundled_weighted cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i live Cd (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646 K169 K81
    hob hout hlen hptr hde hsp hal hi
    (Bound.bundled_key_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF false K646 hlen hsetup.1 hkeys)
    (Bound.bundled_key_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF true K646 hlen hsetup.1 hkeysSaved)
    (Bound.value_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF K169 hlen hsetup.1 hsetup.2 hvalues)
    (Bound.closing bs (i + wsLen (bs.drop i) + 1) baseHL baseF false)
    (Bound.closing bs (i + wsLen (bs.drop i) + 1) baseHL baseF true)
    (Bound.weighted_ignore_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF false K81 hlen hsetup.1 hignored)
    (Bound.weighted_ignore_conditions cfg bs (i + wsLen (bs.drop i) + 1) baseHL baseF true K81 hlen hsetup.1 hignoredSaved)
    N a rF hb0 hloop

theorem f78_bundled_cost_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 43 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (baseHL baseF : Nat) (ptrS sl : UInt32) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hsetup : LedgerSetup baseHL baseF)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K646) (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K169)
    (hignored : WeightedIgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF false) K81) (hignoredSaved : WeightedIgnoreGasCharges cfg bs (Bound bs (i + wsLen (bs.drop i) + 1) baseHL baseF true) K81)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ∗
      A 228 ↪[wf] FuncInst.wasm types[36]! inst f228 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f78 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          (AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
            n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
            SerdeValueState.scratchPre n 2048 baseHL live baseF de ptrS 0 sl)))
        (fun _ => 40 * cfg.regularOpCost + SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          SerdeStructObjKeyState.member n 2048 ta (A 578) idx de live (Ledger bs baseHL baseF false) (Ledger bs baseHL baseF true) (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hs := object_loop_bundled_weighted (GF := GF) cfg lim (d + 1) types[36]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx out out out out ob bs i live Cd baseHL baseF K646 K169 K81
    hob hout hlen hptr hde hsp hal hi hsetup hkeys hkeysSaved hvalues hignored hignoredSaved N a rF hb0 hloop
  iintro ⟨#HC, #HI, #F228, #Hi⟩
  ihave #S := hs $$ [HC HI]
  · iframe HC HI
  iapply f78_of_object_spec cfg lim d type htype inst mi A n g ta hm (by omega)
  iframe F228 Hi
  iapply (SerdeValueState.spec_repack ?hP ?hQ) $$ S
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Hst, Ho, Hrd, Hdepth, Hvt, Htables, Hkey, Hident, Hscratch⟩
    isplitr
    · ipureintro; exact ha
    iframe Hg Hst Ho Hrd Hdepth
    iapply member_initial n 2048 ta (A 578) idx de ptrS sl live bs baseHL baseF (i + wsLen (bs.drop i) + 1)
    iframe Hvt Htables Hkey Hident Hscratch
  case hQ =>
    intro args rs
    iintro ⟨%hrs, Hg, Hst, Hdepth, %p, %cap, O0, O4, O8, O12, %hp, Hmember, Hrd⟩
    iframe Hg Hst Hdepth O0 O4 O8 O12 Hrd
    isplitr
    · ipureintro; exact hrs
    isplitr
    · ipureintro; exact hp
    iapply member_forget n 2048 ta (A 578) idx de live bs (i + wsLen (bs.drop i) + 1) baseHL baseF .done (bs.length - rF.length) (some (a, p, cap))
    iexact Hmember

end Resource
end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeValueState (scratchPre)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxHeartbeats 32000000 in
theorem f66_bundled_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 44 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hrd : rd.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 432 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K646)
    (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K169)
    (hignored : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K81)
    (hignoredSaved : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 432) 432 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => (975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 432) 432 ∗
          vt n 1057464 idx ta (A 578) ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ cleanLedgerObject n mlen F live a.val.toUTF8.toList p c len)) := by
  iintro ⟨#Hc66, #HC, #HP, #Hdrop, #HIgn⟩
  ihave #Hc66' := Hc66
  iunfold code66 at Hc66'
  icases Hc66' with ⟨#H193c, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77, #F214, #F91, #F228,
    #F78, #F634, #F320, #F68, #F747, #F778⟩
  ihave #Hv := H193c
  iunfold SerdeNextKey.code193 at Hv
  icases Hv with ⟨#Hv, -, -, -, -, -, -, -⟩
  ihave #Hv' := Hv
  iunfold SerdeEnds.endCode at Hv'
  icases Hv' with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold SerdeErrBox.errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha634 := hm.funcs 634 (by decide)
  have ha78 := hm.funcs 78 (by decide)
  have ha320 := hm.funcs 320 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h48 : (sp - 64 + 48).toNat = (sp - 64).toNat + 48 := by simp [UInt32.toNat_add]; omega
  have h12 : (sp - 64 + 12).toNat = (sp - 64).toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hvalue : validAccountIdBytes a.val.toUTF8.toList = true := a.toNear.property
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalue
  have hpos : 0 < a.val.toUTF8.toList.length := by omega
  have hbytes : a.val.toUTF8.toList.length < 2 ^ 32 := by omega
  have hkl : k ≤ bs.length := by omega
  generalize hCS : SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0 = CS
  rw [Nat.add_mul]
  generalize hW : 96 * wsLen (bs.drop k) * cfg.regularOpCost = W
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hsr, Hbs, He, Hw, Hhex, Hkey, Hident⟩
  subst hargs
  -- the frame
  icases stk_split n (sp.toNat - 432) 368 64 $$ Hs with ⟨S368, F64⟩
  rw [show sp.toNat - 432 + 368 = (sp - 64).toNat by omega, show sp.toNat - 432 = (sp - 64).toNat - 368 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨O0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 4 52 $$ F56 with ⟨O8, F52⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4) 8 44 $$ F52 with ⟨O12, F44⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8) 4 40 $$ F44 with ⟨O20, F40⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4) 1 39 $$ F40 with ⟨O24, F39⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1) 7 32 $$ F39 with ⟨X25, F32⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7) 8 24 $$ F32 with ⟨A32, F24⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8) 4 20 $$ F24 with ⟨A40, F20⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4) 4 16 $$ F20 with ⟨A44, F16⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4) 8 8 $$ F16 with ⟨B48, F8⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8) 4 4 $$ F8 with ⟨B56, B60⟩
  rw [show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8 + 4 = (sp - 64).toNat + 60 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8 = (sp - 64).toNat + 56 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 = (sp - 64).toNat + 48 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 = (sp - 64).toNat + 44 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 = (sp - 64).toNat + 40 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 = (sp - 64).toNat + 32 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 = (sp - 64).toNat + 25 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 = (sp - 64).toNat + 24 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 = (sp - 64).toNat + 20 by omega,
    show (sp - 64).toNat + 8 + 4 = (sp - 64).toNat + 12 by omega]
  iunfold stk at O0 O8 O12 O20 O24 B48 B56
  icases O0 with ⟨%o0, %ho0, O0⟩
  icases O8 with ⟨%o8, %ho8, O8⟩
  icases O12 with ⟨%o12, %ho12, O12⟩
  icases O20 with ⟨%o20, %ho20, O20⟩
  icases O24 with ⟨%o24, %ho24, O24⟩
  icases B48 with ⟨%b48, %hb48, B48⟩
  icases B56 with ⟨%b56, %hb56, B56⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Q0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨Q4, Q12⟩
  rw [show out.toNat + 4 + 8 = out.toNat + 12 by omega]
  iunfold sliceRead at Hsr
  icases Hsr with ⟨R0, R4, R8⟩
  ihave R := KeyGet.join64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ [R0 R4]
  · iframe R0 R4
  simp only [f66]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [R8]
  mstep [B56]
  mstep; mstep
  mstep [R]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [B48]
  rw [VecFromElem.storeBytes_pair64]
  ihave B48 := KeyGet.split64 n ((sp - 64).toNat + 48) ptr (UInt32.ofNat bs.length) $$ B48
  icases B48 with ⟨B48, B52⟩
  have s634 := ArgsLeaves.f634_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 64)
    (sp - 64 + 48) ptr (UInt32.ofNat bs.length) 0 o0 o8 o12 o20 o24 ho0 ho8 ho12 ho20 ho24 (by omega) (by omega)
  mstep; mstep; mstep; mstep
  mcall s634 using [B48 B52 B56 O0 O8 O12 O20 O24]
  · iunfold sliceRead
    rw [h48]
    iframe B48 B52 B56 O0 O8 O12 O20 O24
  icases HQ with ⟨%hrs, Hsl, HD⟩
  subst hrs
  clear s634
  iunfold sliceRead at Hsl
  rw [h48]
  icases Hsl with ⟨B48, B52, B56⟩
  ihave B48 := stk_word $$ B48
  ihave B52 := stk_word $$ B52
  ihave B56 := stk_word $$ B56
  ihave OB := stk_join n _ 4 4 $$ [B48 B52]
  · iframe B48 B52
  ihave OB := stk_join n _ 8 4 $$ [OB B56]
  · iframe OB B56
  ihave OB := stk_join n _ 12 4 $$ [OB B60]
  · iframe OB B60
  iunfold stk at OB
  icases OB with ⟨%ob2, %hob2, OB⟩
  iunfold deserializer at HD
  icases HD with ⟨Dsr, D12, D20, D24⟩
  ihave Hrd : SerdeRead.rd n (sp - 64) ptr bs 0 $$ [Dsr Hbs]
  · iunfold SerdeRead.rd
    iframe Hbs
    iexact Dsr
  rw [i64_one]
  ihave D12 := KeyGet.split64 n ((sp - 64).toNat + 12) 1 0 $$ D12
  icases D12 with ⟨D12, D16⟩
  rw [show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega]
  ihave Hsb := SerdeScratchValueDrop.empty_scratch n 2048 mlen live F $$ Hh
  ihave Hscratch : SerdeValueState.scratchPre n 2048 mlen live F (sp - 64) 1 0 0 $$ [D20 D12 D16 Hsb]
  · iunfold SerdeValueState.scratchPre
    iframe D20 D12 D16 Hsb
  ihave Htables : SerdeValueState.tables n $$ [He Hw Hhex]
  · iunfold SerdeValueState.tables
    iframe He Hw Hhex
  have s78 := f78_bundled_cost_weighted (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 64) (sp - 64 + 48) (sp - 64) ptr idx ob2 bs 0 live iprop(emp) mlen F 1 0 K646 K169 K81
    hob2 (by omega) hlen hptr (by omega) (by omega) (by rw [h64]; omega) (by omega)
    hsetup (by simpa only [List.drop_zero, Nat.zero_add] using hkeys) (by simpa only [List.drop_zero, Nat.zero_add] using hkeysSaved) (by simpa only [List.drop_zero, Nat.zero_add] using hvalues) (by simpa only [List.drop_zero, Nat.zero_add] using hignored) (by simpa only [List.drop_zero, Nat.zero_add] using hignoredSaved) N a rest (by simpa using ho) (by simpa using hloop)
  rw [h48, hCS, ← hk] at s78
  ihave #Hobj : SerdeStructObjModelState.code n 2048 inst mi A $$ [H193c HP HC F205 F201 F193 F89 F90 F81 F169 F77]
  · iunfold SerdeStructObjModelState.code
    iframe H193c HP HC F205 F201 F193 F89 F90 F81 F169 F77
  ihave #S78 := s78 $$ [Hobj HIgn F228 Hi]
  · iframe Hobj HIgn F228 Hi
  clear s78
  mstep; mstep; mstep; mstep
  mcall S78 using [Hg S368 OB Hrd D24 Hvt Htables Hkey Hident Hscratch]
  · iframe Hg S368 OB Hrd D24 Hvt Htables Hkey Hident Hscratch
  icases HQ with ⟨%hrs, Hg, S368, D24, %p, %cap, W0, W4, W8, W12, %hp, Hmember, Hrd⟩
  let l := UInt32.ofNat a.val.utf8ByteSize
  iunfold WNear.Binary.SerdeStructObjKeyState.member at Hmember
  icases Hmember with ⟨%⟨hcap, _⟩, Hbytes, Hcore⟩
  iunfold WNear.Binary.SerdeStructObjKeyState.core at Hcore
  icases Hcore with ⟨%hl1, %F1, %scratch, %capS, %slFinal, %⟨hb, _⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  obtain ⟨hlo, hhi, hF1⟩ := Ledger.final_bounds bs mlen F k hl1 F1 true capS hlen hb
  subst hrs
  mcredits (865 * cfg.regularOpCost + W + R)
  iunfold stk at A32 A40
  icases A32 with ⟨%a32, %ha32, A32⟩
  icases A40 with ⟨%a40, %ha40, A40⟩
  rw [show (sp - 64).toNat + 48 + 12 = (sp - 64).toNat + 60 by omega,
    show (sp - 64).toNat + 48 + 8 = (sp - 64).toNat + 56 by omega,
    show (sp - 64).toNat + 48 + 4 = (sp - 64).toNat + 52 by omega]
  mstep; mstep; mstep; mstep
  mstep; mstep [W0]; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep [W12]
  mstep [A40]
  ihave W52 := KeyGet.join64 n ((sp - 64).toNat + 52) p cap $$ [W4 W8]
  · rw [show (sp - 64).toNat + 52 + 4 = (sp - 64).toNat + 56 by omega]; iframe W4 W8
  mstep; mstep
  mstep [W52]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [A32]
  rw [VecFromElem.storeBytes_pair64]
  iunfold SerdeValueState.tables at Htables
  icases Htables with ⟨He, Hw, Hhex⟩
  icases stk_split n ((sp - 64).toNat - 368) 272 96 $$ S368 with ⟨S272, S96⟩
  rw [show (sp - 64).toNat - 368 + 272 = (sp - 64).toNat - 96 by omega]
  have s320 := SerdeEndSuccess.f320_eof (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 64) (sp - 64) ptr bs k (by omega) (by omega) (by omega) hkl hend
  rw [Nat.add_mul, hW] at s320
  ihave #S320 := s320 $$ [F332 F333 F339 Hi]
  · iframe F332 F333 F339 Hi
  clear s320
  mstep
  mcall S320 using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  mcredits (631 * cfg.regularOpCost + R)
  mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep [A32]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [Q4]
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep [Q0]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [A40]
  mstep [Q12]
  have s68 := f68_retained_scratch (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm
    (by omega) Cg 2048 hl1 ((p.toNat, cap.toNat) :: live) F1 (sp - 64) scratch capS slFinal (by omega)
  ihave #S68 := s68 $$ Hdrop
  clear s68
  mstep; mstep; mstep
  mcall S68 using [Hscratch]
  · isplitr
    · ipureintro; trivial
    · iexact Hscratch
  icases HQ with ⟨%hrs, D12, D16, D20, Hheap⟩
  subst hrs
  ihave Hheap := AllocInv.heapInv_mono n 2048 hl1 ((p.toNat, cap.toNat) :: live) (F1 + 1) (F + 43)
    (by omega) $$ Hheap
  ihave Hclean : cleanLedgerObject n mlen F live a.val.toUTF8.toList p cap l $$ [Hbytes Hheap]
  · iunfold cleanLedgerObject
    isplitr
    · ipureintro
      have hs := SerdeAcctHyp.utf8_len a.val
      exact ⟨by rw [hcap, hs], by dsimp [l]; rw [hs], hp⟩
    iframe Hbytes
    iexists hl1
    iframe Hheap
    ipureintro; exact ⟨hlo, hhi⟩
  mcredits (5 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt
  iframe He Hw Hhex Hkey Hident
  iunfold SerdeRead.rd at Hrd
  icases Hrd with ⟨Dsr, Hbs⟩
  iframe Hbs
  ihave R := KeyGet.split64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ R
  icases R with ⟨R0, R4⟩
  isplitl [S272 S96 Dsr D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W12]
  · iunfold sliceRead at Dsr
    icases Dsr with ⟨G0, G4, G8⟩
    ihave S368 := stk_join n ((sp - 64).toNat - 368) 272 96 $$ [S272 S96]
    · rw [show (sp - 64).toNat - 368 + 272 = (sp - 64).toNat - 96 by omega]; iframe S272 S96
    ihave W52 := KeyGet.split64 n ((sp - 64).toNat + 52) p cap $$ W52
    icases W52 with ⟨W52, W56⟩
    ihave G0 := stk_word $$ G0
    ihave G4 := stk_word $$ G4
    ihave G8 := stk_word $$ G8
    ihave D12 := stk_word $$ D12
    ihave D16 := stk_word $$ D16
    ihave D20 := stk_word $$ D20
    ihave D24 := stk_intro $$ D24
    ihave A32 := stk_intro $$ A32
    ihave A40 := stk_word $$ A40
    ihave W0 := stk_word $$ W0
    ihave W52 := stk_word $$ W52
    ihave W56 := stk_word $$ W56
    ihave W12 := stk_word $$ W12
    rw [show (bytes32 p ++ bytes32 cap).length = 8 by simp, show ([128] : List UInt8).length = 1 by rfl,
      show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega,
      show (sp - 64).toNat + 52 + 4 = (sp - 64).toNat + 56 by omega]
    ihave F64 := frame66 n (sp - 64).toNat $$ [G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W56 W12]
    · iframe G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W56 W12
    ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 368 + 368 by omega) $$ F64
    iapply stk_join n ((sp - 64).toNat - 368) 368 64
    iframe S368 F64
  isplitl [R0 R4 R8]
  · iunfold sliceRead
    iframe R0 R4 R8
  iexists p, cap, l
  ihave Q4 := KeyGet.split64 n (out.toNat + 4) p cap $$ Q4
  icases Q4 with ⟨Q4, Q8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  iframe Q0 Q4 Q8 Q12 Hclean


end Resource
end WNear.Binary.SerdeObjectPrefix
namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeValueState (scratchPre)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
theorem f65_bundled_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 45 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K646)
    (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K169)
    (hignored : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K81)
    (hignoredSaved : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => 45 * cfg.regularOpCost + ((975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ cleanLedgerObject n mlen F live a.val.toUTF8.toList p c len)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  let P : IProp GF := iprop(stk n (sp.toNat - 448) 432 ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n 2048 mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
    n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
    n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes)
  let Q : List Value → IProp GF := fun _ => iprop(stk n (sp.toNat - 448) 432 ∗ vt n 1057464 idx ta (A 578) ∗
    n ↦[wms][ ptr.toNat ] bs ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
    n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
    ∃ (p c len : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
      n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] len ∗
      cleanLedgerObject n mlen F live a.val.toUTF8.toList p c len)
  let K := (975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost + SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0
  have hs := f66_bundled_weighted (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 16) out (sp - 16) ptr idx ob bs a rest N k mlen F live hob hout
    (by omega) hlen hptr (by omega) (by rw [h16]; omega) K646 K169 K81 hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hk hend
  rw [show (sp - 16).toNat - 432 = sp.toNat - 448 by omega] at hs
  have hs' : code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ⊢
      MFunSpec cfg lim (d + 1) types[14]! inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 (sp - 16)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          sliceRead n (sp - 16) ptr (UInt32.ofNat bs.length) 0 ∗ P))
        (fun _ => K)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          (∃ a b c : UInt32, sliceRead n (sp - 16) a b c) ∗ Q rs)) := by
    apply hs.trans
    apply SerdeValueState.spec_repack
    · intro args
      dsimp only [P]
      iintro ⟨%ha, Hg, Hrd, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, Hkey, Hident⟩
      iframe Hg Hs Hvt Hheap Ho Hrd Hbs He Hw Hhex Hkey Hident
      ipureintro; exact ha
    · intro args rs
      dsimp only [Q]
      iintro ⟨%hrs, Hg, Hs, Hvt, Hrd, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
      iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident Hresult
      isplitr
      · ipureintro; exact hrs
      iexists ptr, UInt32.ofNat bs.length, 0
      iexact Hrd
  have key := ArgsLeaves.f65_of_66 (GF := GF) cfg lim d type htype inst mi n g hm.mem hm.glob (A 66) (A 644)
    (hm.funcs 66 (by decide)) (hm.funcs 644 (by decide)) (by omega) Cg gt sp out ptr (UInt32.ofNat bs.length)
    (by omega) P K Q
  iintro ⟨#H66, #HC, #HP, #HD, #HIgn, #F644, #F66, #Hi⟩
  ihave #S66 := hs' $$ [H66 HC HP HD HIgn]
  · iframe H66 HC HP HD HIgn
  ihave #S65 := key $$ [F644 F66 Hi S66]
  · iframe F644 F66 Hi S66
  iapply SerdeValueState.spec_repack ?hPre ?hPost $$ S65
  case hPre =>
    intro args
    dsimp only [P]
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, Hkey, Hident⟩
    icases stk_split n (sp.toNat - 448) 432 16 $$ Hs with ⟨Hs, Hs16⟩
    ihave Hs16 := stk_addr (show sp.toNat - 448 + 432 = sp.toNat - 16 by omega) $$ Hs16
    iframe Hg Hs16 Hs Hvt Hheap Ho Hbs He Hw Hhex Hkey Hident
    ipureintro; exact ha
  case hPost =>
    intro args rs
    dsimp only [Q]
    iintro ⟨%hrs, Hg, Hs16, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
    iframe Hg Hvt Hbs He Hw Hhex Hkey Hident Hresult
    isplitr
    · ipureintro; exact hrs
    ihave Hs16 := stk_addr (show sp.toNat - 16 = sp.toNat - 448 + 432 by omega) $$ Hs16
    iapply stk_join n (sp.toNat - 448) 432 16
    iframe Hs Hs16



end Resource
end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeValueState (scratchPre)
open WNear.Binary.LookupMapOps (HeapRoomK)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem f65_bundled_room_weighted (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 45 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K646)
    (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K169)
    (hignored : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K81)
    (hignoredSaved : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => 45 * cfg.regularOpCost + ((975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ hl', ⌜LookupMapOps.HeapRoomK 6 hl' 2048⌝ ∗
          BalanceOf297AbsentCall.okAtFixed n out a live hl' (F + 43))) := by
  apply (f65_bundled_weighted cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N k mlen F live hob hout hlen hptr hsp hal K646 K169 K81
    hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hk hend).trans
  apply ParseStrSuccess.spec_post
  intro args rs
  iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, %p, %cap, %len, O0, O4, O8, O12, Hclean⟩
  iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident
  isplitr
  · ipureintro; exact hrs
  iapply ledger_result_room n mlen F live out p cap len a hsetup
  iframe O0 O4 O8 O12 Hclean


set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem bundled_parser_contract_weighted (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta Cg : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (sp out ptr idx : UInt32) (ob bs rest : List UInt8) (a : WNear.AccountId) (N mlen F : Nat)
    (live : List (Nat × Nat)) (hd : d + 45 < lim.maxCallDepth)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K646)
    (hkeysSaved : BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K169)
    (hignored : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K81)
    (hignoredSaved : WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.ParserCallContract (GF := GF) cfg lim d inst mi A n g ta Cg gt sp out ptr idx
      ob bs a mlen live F (ledgerParserCost cfg K646 K169 K81 bs rest N) (F + 43)
      (ledgerParserCode n inst mi A) (ledgerParserStatics n) := by
  unfold BalanceOf297AbsentCall.ParserCallContract
  have hs := f65_bundled_room_weighted (GF := GF) cfg lim d types[31]! rfl inst mi A n g ta hm hd Cg gt
    sp out ptr idx ob bs a rest N (bs.length - rest.length) mlen F live hob hout hlen hptr hsp hal K646 K169 K81 hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop rfl hend
  unfold ledgerParserCode
  simp only [ledgerParserCost, Nat.add_assoc]
  apply hs.trans
  apply SerdeValueState.spec_repack
  · intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, HFr⟩
    iunfold ledgerParserStatics at HFr
    icases HFr with ⟨Hkey, Hident⟩
    iframe Hg Hs Hvt Hheap Ho Hbs He Hw Hhex Hkey Hident
    ipureintro; exact ha
  · intro args rs
    iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
    iunfold ledgerParserStatics
    iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident Hresult
    ipureintro; exact hrs



set_option maxRecDepth 100000 in
/-- General object parsing supplies the same checked family used by the full balance pipeline. -/
theorem bundled_parser_family_weighted (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (bs rest : List UInt8) (a : WNear.AccountId) (N F : Nat) (K646 K169 K81 : Nat → Nat)
    (hlen : bs.length ≤ 4194304) (hF : 1 ≤ F)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) len F false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges cfg bs (Bound bs (wsLen bs + 1) len F true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges cfg bs (Bound bs (wsLen bs + 1) len F false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) len F false) K81)
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) len F true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.ParserFamily (GF := GF) cfg lim inst mi A n g ta gt bs a F
      (ledgerParserCost cfg K646 K169 K81 bs rest N) (F + 43) (ledgerParserCode n inst mi A) := by
  intro Cg d sp out ptr idx ob len live hd hob hout _ hptr hsp hal hL
  exact bundled_parser_contract_weighted cfg lim d inst mi A n g ta Cg hm gt sp out ptr idx ob bs rest a N len F live
    hd hob hout hlen hptr hsp hal K646 K169 K81 (input_ledger_bounds bs len F hlen hF hL)
    (hkeys len hL) (hkeysSaved len hL) (hvalues len hL) (hignored len hL) (hignoredSaved len hL) ho hloop hend

end Resource

theorem bundled_deployed_parser_provider_weighted (cfg : RuntimeConfig) (bs rest : List UInt8) (a : WNear.AccountId)
    (N : Nat) (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges cfg.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges cfg.wasm bs (Bound bs (wsLen bs + 1) len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges cfg.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges cfg.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K81)
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges cfg.wasm bs (Bound bs (wsLen bs + 1) len 1 true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.DeployedParserProvider cfg bs a (ledgerParserCost cfg.wasm K646 K169 K81 bs rest N) 44 := by
  intro h _
  apply BalanceOf297AbsentCall.parser_family_mono cfg.wasm execLimits 0 wInst id 0 0 0
    InitialState.g0.type bs a 1 (ledgerParserCost cfg.wasm K646 K169 K81 bs rest N) 44
    (FromSliceSpec.codeCtx cfg h) (ledgerParserCode 0 0 wInst id) (ledger_parser_code_of_context cfg h)
  exact bundled_parser_family_weighted cfg.wasm execLimits 0 wInst id 0 0 0 Interface.wInst_ifaceMod InitialState.g0.type
    bs rest a N 1 K646 K169 K81 hlen (by decide) hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend

open NearInterface ContractModel in
/-- The original model-budget witness is coupled to this actual general-object parser. -/
theorem bundled_provider_plan_weighted (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N size : Nat)
    (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K81)
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw modelSt ctx S a
      (ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N) 44) :
    BalanceOf297AbsentCall.AbsentParserPlan cfg size raw modelSt ctx S a bs := by
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  exact ⟨ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N, 44, by omega, hpos,
    bundled_deployed_parser_provider_weighted ctx.protocol bs rest a N K646 K169 K81 hlen
      hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend, hbudget⟩

open NearInterface ContractModel in
theorem bundled_refines_init_weighted (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      BundledKeyGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K81)
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      WeightedIgnoreGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw (some S) ctx S a
      (ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N) 44)
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (ha : a ∉ S.registered) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hPlan := bundled_provider_plan_weighted cfg ctx raw (some S) S a bs rest N size K646 K169 K81 hlen
    hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend hbudget
  exact BalanceOf297AbsentCall.provider_plan_refines_init cfg size codeOf raw ctx S a bs
    hp hwf hm hl hPlan hargs hrep ha



end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeRead (wsLen)
open Wasm Wasm.Near WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.SerdeObjectMixedTrace
open NearInterface ContractModel in
theorem fully_weighted_bundled_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw (some S) ctx S a
      (ledgerParserCost ctx.protocol.wasm (selectedBundledKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1) (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1) (selectedWeightedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) bs rest N) 44)
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (ha : a ∉ S.registered) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact bundled_refines_init_weighted cfg size codeOf raw ctx S a bs rest N
    (selectedBundledKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedWeightedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) hlen hp hwf hm hl
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    (fun len _ => Bound.selected_value_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1)
    (fun len _ => Bound.selected_weighted_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_weighted_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    ho hloop hend hbudget hargs hrep ha

end WNear.Binary.SerdeObjectPrefix
