import Bridge.Methods.Code296
import Bridge.Functions.DepositBody234None
import Bridge.Functions.DepositPanicsFull

/-!
# The code `near_deposit` (234) runs, from the instantiated store

`codeDep_of`: the persistent function cells of `wStore`, the instance and the memory limit give
`DepositBody234.code234` (the prologue, `state_read`, `unwrap_or_default`, 232 with everything it
calls, `state_write`), `DepositPanicsFull.codePanics` (the three Rust panics) and
`FtTotalSupply.codeP` (`PanicOnDefault`'s path) for `wInst`.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 256000000 in
/-- **The code of `near_deposit`**, from the store's function cells. -/
theorem codeDep_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
      DepositBody234.code234 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 (some 2048) ∗
        DepositPanicsFull.codePanics cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 (some 2048) ∗
        FtTotalSupply.codeP cfg.fees.numExtraBytesRecord 0 wInst id := by
  iintro ⟨#HF, #Hi, #Hm⟩
  simp only [
    AllocTwo.code310, AllocTwoWalk.code575, AllocTwoWalk.code7, AllocZeroed.allocCode, AllocZeroedF.code575F,
    BorshBytes.bytesCode, BorshContract.contractCode, BorshContract.sliceCode, BorshFT.ftCode, BorshInt.rdCode,
    BorshSer.ftSerCode, BorshSer.ser163Code, BorshSer.ser164Code, BorshSer.serCode,
    DepositBody.code232, DepositBody234.code234, DepositLog.code846, DepositLog.logCode,
    DepositLog.strArgCode, DepositPanicsFull.codePanics, DepositSegAll.codeSeg, DepositTail.tailCode,
    DropVec.dropCode, EnvDeposit.dCode, EnvGetters.dCode, EnvGetters.uCode,
    EnvPredecessor.pCode, FmtDisplay.fmtCode, FmtSink.sinkCode, FmtSinkRe.sinkCodeR,
    FtTotalSupply.codeA, FtTotalSupply.codeB, FtTotalSupply.codeC, FtTotalSupply.codeP,
    GetFmt.code826, GetSink.getCode, Interface.ifaceCode,
    InternalDeposit.code405, InternalDeposit.code406, InternalDeposit.code409, LogStr.lCode,
    LookupMapBorsh.code376, LookupMapBorsh.code377, LookupMapBorsh.code395, LookupMapBorsh.code397,
    LookupMapBorsh.code398, LookupMapContains.code394, LookupMapContains.code396, LookupMapGet.code399,
    LookupMapGet.code400, LookupMapInsert.code391, LookupMapInsertSome.code391s, LookupMapInsertSome.code401s,
    LookupMapLeaves.code392, LookupMapLeaves.code510, LookupMapLeaves.code519, LookupMapLeaves.rr550Code,
    LookupMapLeavesF.rr550CodeF, LookupMapOps.code401, LookupMapOps.code402,
    PanicBegin.panicCode', PanicDisplay.code885, PanicDisplayMsg.code885M,
    PanicFmt.code817, PanicFmt.code859, PanicHook.hookCode, PanicStr.panicCode, PredecessorId.code512,
    PredecessorId.code526, ReadRegister.ifaceCodeR, ReadRegister.rrCode, ReadRegisterF.rrCodeF,
    StateRead.stateCode, StateWrite.swCode, StorageHasKey.hCode,
    StorageReadWrap.srCode, StorageReadWrapF.srCodeF, StorageWrite.wCode, StrSinkGrow.strCode, ToString.tsCode,
    ToStrMsg.codeTSM, ToStrPay.codeTS, ToVec.tvCode, VecAppend.appCode,
    VecFromElem.vecCode, VecFromElemF.vecCodeF, VecGrow.growCode, VecGrow.reallocCode, VecGrow.waCode,
    VecWithCap.vecCode2, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h _ _ ?_ ?_ <;> first | iexact HF | decide | simp [wStore, wHosts])
    | isplitl [])

end Leaves

end WNear.Binary.InitialState
