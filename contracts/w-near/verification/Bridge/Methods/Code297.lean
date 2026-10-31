import Bridge.Methods.Code296
import Bridge.Functions.BalanceOf297ParserRoom

/-! Persistent code resources for the copied-array absent-account path of function 297.
Each component is extracted from the instantiated store's function cells. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

section
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def code297Input (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(FtTotalSupply.codeA inst mi A ∗ EnvInput.inCode e inst mi A n 2048 mx ∗
    A 527 ↪[wf] FuncInst.wasm types[0]! inst f527)

def code297Parser (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) : IProp GF :=
  iprop(SerdeFromTrait.code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
    ParseStr.code646 n 2048 inst mi A ∗
    A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
    A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157)

def code297Lookup (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(StateReadLenF.stateCodeF e inst mi A n 2048 mx ∗
    A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
    A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
    BalanceOfAbsent.code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293)

def code297Return (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) : IProp GF :=
  iprop(ToVec.tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
    A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
    A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
    DropVec.dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68)

def code297 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(code297Input e inst mi A n mx ∗ code297Parser inst mi A n ∗
    code297Lookup e inst mi A n mx ∗ code297Return inst mi A n ∗
    Interface.ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (code297 (GF := GF) e inst mi A n mx) := by
  unfold code297 code297Input code297Parser code297Lookup code297Return
  infer_instance

end
end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.InitialState
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open WNear.Binary.BalanceOf297AbsentCall

section
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- The input code resources from the instantiated function cells. -/
theorem code297_input_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
    code297Input cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := ReadRegister.wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := Interface.wStore_hosts cfg h
  have h6 := EnvInput.wStore_input cfg h
  simp only [code297Input, WNear.Binary.AllocZeroed.allocCode, WNear.Binary.VecFromElem.vecCode, WNear.Binary.ReadRegister.rrCode, WNear.Binary.Interface.ifaceCode, WNear.Binary.ReadRegister.ifaceCodeR, WNear.Binary.FtTotalSupply.codeA, WNear.Binary.EnvInput.inCode, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 0 _ (by decide) h0; iexact HF)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 6 _ (by decide) h6; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | isplitl [])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- The parser code resources from the instantiated function cells. -/
theorem code297_parser_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
    code297Parser 0 wInst id 0 := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := ReadRegister.wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := Interface.wStore_hosts cfg h
  have h6 := EnvInput.wStore_input cfg h
  simp only [code297Parser, WNear.Binary.SerdeEnds.endCode, WNear.Binary.SerdeNextKey.code193, WNear.Binary.ScratchGrow.sgCode, WNear.Binary.AllocTwo.code310, WNear.Binary.SerdeDeStr.code380, WNear.Binary.SerdeString.strCode, WNear.Binary.SerdeFromTrait.code66, WNear.Binary.SerdeEsc.eofCode, WNear.Binary.ParseEscape.escCode, WNear.Binary.SerdeErrBox.errCode, WNear.Binary.SerdeAccountId.code169, WNear.Binary.VecGrow.reallocCode, WNear.Binary.DropVec.dropCode, WNear.Binary.ParseStr.code646, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 0 _ (by decide) h0; iexact HF)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 6 _ (by decide) h6; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | isplitl [])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- The lookup code resources from the instantiated function cells. -/
theorem code297_lookup_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
    code297Lookup cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := ReadRegister.wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := Interface.wStore_hosts cfg h
  have h6 := EnvInput.wStore_input cfg h
  simp only [code297Lookup, WNear.Binary.AllocZeroed.allocCode, WNear.Binary.BorshBytesF.bytesCode, WNear.Binary.LookupMapBorsh.code376, WNear.Binary.LookupMapBorsh.code395, WNear.Binary.VecFromElem.vecCode, WNear.Binary.ReadRegister.rrCode, WNear.Binary.Interface.ifaceCode, WNear.Binary.ReadRegisterF.rrCodeF, WNear.Binary.BorshFTF.ftCode, WNear.Binary.BorshContractF.contractCode, WNear.Binary.BalanceOfAbsent.code293, WNear.Binary.BorshSer.serCode, WNear.Binary.LookupMapLeaves.code519, WNear.Binary.LookupMapLeaves.code510, WNear.Binary.BalanceOfAbsent.code415, WNear.Binary.StorageReadWrapF.srCodeF, WNear.Binary.LookupMapLeaves.code392, WNear.Binary.LookupMapGet.code399, WNear.Binary.BorshContractF.sliceCode, WNear.Binary.ReadRegister.ifaceCodeR, WNear.Binary.VecAppend.appCode, WNear.Binary.DropVec.dropCode, WNear.Binary.BorshInt.rdCode, WNear.Binary.VecWithCap.vecCode2, WNear.Binary.LookupMapGet.code400, WNear.Binary.LookupMapBorsh.code377, WNear.Binary.LookupMapBorsh.code398, WNear.Binary.StateReadLenF.stateCodeF, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 0 _ (by decide) h0; iexact HF)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 6 _ (by decide) h6; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | isplitl [])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- The return code resources from the instantiated function cells. -/
theorem code297_return_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
    code297Return 0 wInst id 0 := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := ReadRegister.wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := Interface.wStore_hosts cfg h
  have h6 := EnvInput.wStore_input cfg h
  simp only [code297Return, WNear.Binary.FmtDisplay.fmtCode, WNear.Binary.AllocZeroed.allocCode, WNear.Binary.FmtSink.sinkCode, WNear.Binary.SerializeStr.serCode, WNear.Binary.ToVec.tvCode, WNear.Binary.ToString.tsCode, WNear.Binary.SerializeStr.escCode, WNear.Binary.VecAppend.appCode, WNear.Binary.DropVec.dropCode, WNear.Binary.VecWithCap.vecCode2, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 0 _ (by decide) h0; iexact HF)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 6 _ (by decide) h6; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | isplitl [])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- The interface code resources from the instantiated function cells. -/
theorem code297_interface_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
    Interface.ifaceCode cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := ReadRegister.wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := Interface.wStore_hosts cfg h
  have h6 := EnvInput.wStore_input cfg h
  simp only [WNear.Binary.Interface.ifaceCode, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 0 _ (by decide) h0; iexact HF)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 6 _ (by decide) h6; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | isplitl [])

/-- All code resources required by the copied-array absent-account body. -/
theorem code297_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
    code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) := by
  iintro ⟨#HF, #Hi, #Hm⟩
  iunfold code297
  repeat' (first
    | (iapply code297_input_of cfg h; iframe HF Hi Hm)
    | (iapply code297_parser_of cfg h; iframe HF Hi Hm)
    | (iapply code297_lookup_of cfg h; iframe HF Hi Hm)
    | (iapply code297_return_of cfg h; iframe HF Hi Hm)
    | (iapply code297_interface_of cfg h; iframe HF Hi Hm)
    | iexact Hi
    | isplitl [])

/-- Extract the code while retaining the initial table, memory and host resources. -/
theorem startCode297_gen (cfg : RuntimeConfig) (h : NearState) (m : Memory) (L : Nat) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗
        Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗
      memR m 0 0 L : IProp GF) ⊢
    |==> (code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗
      0 ↪[inst] wInst ∗ 0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
      gasPt h.gas h.gasProfile h.actionProfile ∗ ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ memR m 0 0 L) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave #Hcode := code297_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  imodintro
  iframe Hcode HL Hg Hh Hgas HT HM
  iunfold instPt
  iexact Hi

/-- The exact code resources from ownership of the instantiated store, preserving the rest for entry setup. -/
theorem startCode297 (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
    |==> (code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗
      0 ↪[inst] wInst ∗ 0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
      gasPt h.gas h.gasProfile h.actionProfile ∗ ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗
      memR wDataMem 0 0 memLen) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startCode297_gen cfg h wDataMem memLen))

end
end WNear.Binary.InitialState
