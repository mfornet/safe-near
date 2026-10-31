import Bridge.Methods.FtBalanceOfNoneGas

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic NearInterface WNear.Binary
open WNear.Binary.FtTotalSupply (ReadNone)
open WNear.Binary.FtTotalSupplyMethod (notInitMsg)

theorem readNone_inputHost {h : NearState} {tr : Near.TrieOverlay.State} (hr : ReadNone h tr) :
    ReadNone (inputHost h 0) tr :=
  ⟨hr.value, hr.acc, hr.keyLen, hr.trie, hr.zero, hr.link, hr.proof, hr.logFits, hr.readByte⟩

theorem none_pre_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (a : WNear.AccountId)
    (bs : List UInt8) (hlen : bs.length ≤ 4194304) (hargs : ctx.args = bs) (hwf : ctx.WF raw)
    (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = none) :
    (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none (.ftBalanceOf a)) → NonePre bs ctx.trie (erase (hostOf ctx raw))) ∧
      NonePre bs ctx.trie (eraseP (hostOf ctx raw)) := by
  have hlim : withinLimit (hostOf ctx raw).config.maxRegisterLen bs.length = true := by
    change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) bs.length = true
    have hi := hl.register
    simpa [withinLimit] using (show bs.length ≤ ctx.protocol.wasm.limits.maxRegisterSize by omega)
  refine ⟨fun hroom => ⟨hargs, hlim, readNone_inputHost ?_⟩, ⟨hargs, hlim, readNone_inputHost ?_⟩⟩
  · apply FtTotalSupplyMethod.readNone_of ctx raw hwf hl hc hval (erase (hostOf ctx raw)) rfl
    exact (FtTotalSupplyMethod.budget_of_room hwf hroom _ rfl rfl).mono (FtTotalSupplyMethod.lookup_le_proofBound ctx)
  · apply FtTotalSupplyMethod.readNone_of ctx raw hwf hl hc hval (eraseP (hostOf ctx raw)) rfl
    intro size hsz
    cases hsz

theorem none_post_panicHost {tr : Near.TrieOverlay.State} {e0 e : NearState}
    (h0 : e0.lastExecutionIssue = none) (hp : noneMethodPost tr e0 e) : PanicHost notInitMsg e := by
  obtain ⟨h1, hq, rfl⟩ := hp
  obtain ⟨-, -, -, hi⟩ := FtTotalSupply.storageReadPost_fields hq
  exact ⟨rfl, hi.trans h0⟩

theorem none_post_logs {tr : Near.TrieOverlay.State} {e0 e : NearState}
    (h0 : e0.logs = []) (hp : noneMethodPost tr e0 e) : logsOf e = [] := by
  obtain ⟨h1, hq, rfl⟩ := hp
  obtain ⟨-, hl, -, -⟩ := FtTotalSupply.storageReadPost_fields hq
  show (h1.logs.map _) = []
  rw [hl]
  change e0.logs.map _ = []
  rw [h0]; rfl

theorem none_model_agreement (cfg : WNear.Config) (ctx : Context) (a : WNear.AccountId) (e : NearState)
    (hl : logsOf e = []) : AgreesPanic (WNear.wnear cfg) notInitMsg e ((WNear.wnear cfg).step ctx none (.ftBalanceOf a)) :=
  ⟨_, rfl, rfl, hl.symm⟩

/-- Exact remaining generic loading/activation/body allowance, without a replacement gas budget. -/
def NoneProviderModelBudget (cfg : WNear.Config) (size : Nat) (raw : RawStorage)
    (modelSt : Option WNear.State) (ctx : Context) (a : WNear.AccountId) (parseGas : Nat) : Prop :=
  chargesUse (hostOf ctx raw) (loadingCharges size) + noneProviderMethodCost ctx.protocol parseGas (erase (hostOf ctx raw)) ≤
    (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)

open ContractModel in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Full uninitialized receipt refinement with the exact deployed parser provider explicitly named. -/
theorem provider_none_refines (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (a : WNear.AccountId) (bs : List UInt8) (parseGas outF : Nat)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304) (hpos : 0 < bs.length)
    (hProvider : NoneDeployedParserProvider ctx.protocol bs a parseGas outF)
    (hparse : parseGas ≤ 1000000000000 + (2215 + 470 * bs.length) * ctx.protocol.wasm.regularOpCost) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨ (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  have hval : (hostOf ctx raw).storage WNear.stateKey = none := by
    rw [hraw]; exact FtTotalSupplyMethod.hostOf_storage_empty ctx _
  obtain ⟨hpre, hpreP⟩ := none_pre_of_ctx cfg ctx raw a bs hlen hargs hwf hl hc hval
  have hv : (hostOf ctx raw).storage StateRead.stateKey = none := by simpa only [StateRead.stateKey_eq] using hval
  exact method_refines_callP (WNear.wnear cfg) size codeOf raw none ctx (.ftBalanceOf a) (NonePre bs ctx.trie)
    (noneProviderMethodCost ctx.protocol parseGas) (noneMethodPost ctx.trie) FtTotalSupplyMethod.notInitMsg hp hwf
    (by rw [hm]; decide) (by rw [hm]; exact BalanceOf297AbsentCall.export_297) BalanceOf297AbsentCall.funcType_297 (by decide) (by decide)
    (provider_none_runs ctx.protocol a bs parseGas outF ctx.trie (by omega) hpos hProvider) hpre hpreP
    (fun e he => none_post_panicHost rfl he) (fun e he => none_post_panicHost rfl he)
    (fun e he => none_model_agreement cfg ctx a e (none_post_logs rfl he))
    (fun e he => none_model_agreement cfg ctx a e (none_post_logs rfl he))
    (none_model_budget_of_parser_linear cfg ctx raw none a bs parseGas size hc hsize hargs hlen hparse hv)
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic NearInterface ContractModel WNear.Binary
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem provider_none_refines_with_budget (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (a : WNear.AccountId) (bs : List UInt8) (parseGas outF : Nat)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304) (hpos : 0 < bs.length)
    (hProvider : NoneDeployedParserProvider ctx.protocol bs a parseGas outF)
    (hbudget : NoneProviderModelBudget cfg size raw none ctx a parseGas) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨ (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  have hval : (hostOf ctx raw).storage WNear.stateKey = none := by
    rw [hraw]; exact FtTotalSupplyMethod.hostOf_storage_empty ctx _
  obtain ⟨hpre, hpreP⟩ := none_pre_of_ctx cfg ctx raw a bs hlen hargs hwf hl hc hval
  have hv : (hostOf ctx raw).storage StateRead.stateKey = none := by simpa only [StateRead.stateKey_eq] using hval
  exact method_refines_callP (WNear.wnear cfg) size codeOf raw none ctx (.ftBalanceOf a) (NonePre bs ctx.trie)
    (noneProviderMethodCost ctx.protocol parseGas) (noneMethodPost ctx.trie) FtTotalSupplyMethod.notInitMsg hp hwf
    (by rw [hm]; decide) (by rw [hm]; exact BalanceOf297AbsentCall.export_297) BalanceOf297AbsentCall.funcType_297 (by decide) (by decide)
    (provider_none_runs ctx.protocol a bs parseGas outF ctx.trie (by omega) hpos hProvider) hpre hpreP
    (fun e he => none_post_panicHost rfl he) (fun e he => none_post_panicHost rfl he)
    (fun e he => none_model_agreement cfg ctx a e (none_post_logs rfl he))
    (fun e he => none_model_agreement cfg ctx a e (none_post_logs rfl he))
    hbudget
end WNear.Binary.BalanceOf297NoneCall
