import Bridge.Functions.SerdeIgnExecution

namespace WNear.Binary.SerdeIgnObject
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.SerdeIgnExecution
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructObjKeyState (Bounds core member KeyConditions)
open WNear.Binary.SerdeStructObjValueState (ValueConditions)
open WNear.SerdeStructModel

def ignored (bs : List UInt8) : Option (Unit × List UInt8) := (WNear.IgnoreModel.vSkip bs).map fun r => ((), r)

theorem ignored_agrees : WNear.SerdeStructModel.Agrees ignored WNear.SerdeStructModel.valueSkip :=
  WNear.IgnoreModel.vSkip_agrees

/-- Exact remaining closure obligations for reachable ignored-member states and the chosen cost allowance. -/
def IgnoreConditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (K : Nat → Nat) (B : Bounds) : Prop :=
  ∀ i hl F cap r ops, B i hl F cap → cap.toNat < 2 ^ 25 → i ≤ bs.length →
    bs[i + wsLen (bs.drop i)]? = some 0x3A →
    SerdeIgnMachineTrace.trace (bs.drop (i + wsLen (bs.drop i) + 1)) = some (r, ops) →
    Room maxP hl cap 0 ops ∧
    (166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap 0 ops ≤ K (i + wsLen (bs.drop i) + 1) ∧
    ∀ hl', HeapTrace hl cap 0 ops hl' →
      B (bs.length - r.length) hl' (SerdeIgnTrace.endFreeBound F cap 0 ops) (SerdeIgnTrace.endState cap 0 ops).1 ∧
      (SerdeIgnTrace.endState cap 0 ops).1.toNat < 2 ^ 25

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The general object ignored-reader interface composes from the full actual reader under named closure obligations. -/
theorem ignoreHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : Bounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hconditions : IgnoreConditions cfg maxP bs K B) (hconditionsSaved : IgnoreConditions cfg maxP bs K Bsaved)
    (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code n maxP inst mi A) :
    SerdeStructObjState.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs ignored K
      (member n maxP ta (A 578) idx de live B Bsaved) Cd := by
  intro d s i rest seen hd hsp hsend hi hcolon hmodel
  unfold ignored at hmodel
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
  icases SerdeStructObjKeyState.seen_core n maxP ta (A 578) idx de s live B Bsaved i seen $$ Hseen with
    ⟨%C, %lv, %hC, Hcore, Hsaved⟩
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %p, %cap, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  have hcond : IgnoreConditions cfg maxP bs K C := by
    rcases hC with rfl | rfl
    · exact hconditions
    · exact hconditionsSaved
  obtain ⟨hroom, hgas, hbound⟩ := hcond i hl F cap rest ops hb hcap hi hcolon htrace
  iunfold SerdeValueState.tables at Htables
  icases Htables with ⟨Hesc, Hwidth, Hhex⟩
  have callIgnore := (f201_traced (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt s (s + 32) de ptr p cap sl idx
    maxP hl F lv bs rest ops i
    (iprop(n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
    (by omega) hde (by rw [hs32]; omega) hlen hptr hi hcolon (by omega) htrace hroom).trans
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
    obtain ⟨hb', hcap'⟩ := hbound hl' hheap
    iframe Hc M32 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H144 H160]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 144 160
      rw [show s.toNat - 304 + 144 = s.toNat - 160 by omega]
      iframe H144 H160
    iapply Hsaved $$ %(bs.length - rest.length)
    iunfold core
    iexists hl', SerdeIgnTrace.endFreeBound F cap 0 ops, p', (SerdeIgnTrace.endState cap 0 ops).1, 0
    iframe Hvt Hkey Hident
    isplitr
    · ipureintro; exact ⟨hb', hcap'⟩
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

set_option maxRecDepth 100000 in
/-- The existing full object loop consumes the checked ignored-reader constructor. -/
theorem object_loop (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i maxP : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : Bounds) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : KeyConditions cfg maxP bs B K646) (hkeysSaved : KeyConditions cfg maxP bs Bsaved K646)
    (hvalues : ValueConditions cfg maxP bs B Bsaved K169)
    (hmono : ∀ i j hl F cap, i ≤ j → B i hl F cap → B j hl F cap)
    (hmonoSaved : ∀ i j hl F cap, i ≤ j → Bsaved i hl F cap → Bsaved j hl F cap)
    (hignored : IgnoreConditions cfg maxP bs K81 B)
    (hignoredSaved : IgnoreConditions cfg maxP bs K81 Bsaved)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n maxP inst mi A ∗ (SerdeIgnMember.code n maxP inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n maxP ta (A 578) idx de live B Bsaved (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n maxP ta (A 578) idx de live B Bsaved (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hcode : iprop(SerdeStructObjModelState.code n maxP inst mi A ∗ (SerdeIgnMember.code n maxP inst mi A ∗ Cd)) ⊢
      SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
        A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code n maxP inst mi A := by
    iintro ⟨#Hobj, #Hmember, _⟩
    iunfold SerdeStructObjModelState.code at Hobj
    icases Hobj with ⟨#C193, -, -, -, -, -, #F89, -, #F81, -⟩
    iunfold SerdeNextKey.code193 at C193
    icases C193 with ⟨#Cend, -⟩
    iframe Cend F89 F81 Hmember
  have hignore := ignoreHyp cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr bs live B Bsaved K81 hlen hptr (by omega)
    hignored hignoredSaved iprop(SerdeStructObjModelState.code n maxP inst mi A ∗ (SerdeIgnMember.code n maxP inst mi A ∗ Cd)) hcode
  exact SerdeStructObjModelState.f228_obj_model cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx x2 x3 x4 x5
    ob bs i maxP live iprop(SerdeIgnMember.code n maxP inst mi A ∗ Cd) B Bsaved K646 K169 K81 ignored ignored_agrees
    hob hout hlen hptr hde hsp hal hi hkeys hkeysSaved hvalues hmono hmonoSaved hignore N a rF hb0 hloop

end Proof
end WNear.Binary.SerdeIgnObject
