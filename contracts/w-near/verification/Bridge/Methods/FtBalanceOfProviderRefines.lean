import Bridge.Methods.FtBalanceOfProviderRun
import Bridge.Methods.FtBalanceOfCopiedPre

/-! Actual-code parser providers, whole-method resource composition and receipt refinement.
The general provider and model-budget obligations remain explicit. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open NearInterface ContractModel in
/-- The original model allowance must cover actual loading, activation and provider-based body costs. -/
noncomputable def ProviderModelBudget (cfg : WNear.Config) (size : Nat) (raw : RawStorage)
    (modelSt : Option WNear.State) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (parseGas outF : Nat) : Prop :=
  chargesUse (hostOf ctx raw) (loadingCharges size) +
    providerMethodCost ctx.protocol S a parseGas outF (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_absent_refines_with_obligations (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8) (parseGas outF : Nat)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of")
    (hlen : bs.length < 2 ^ 24)
    (hpos : 0 < bs.length)
    (hProvider : DeployedParserProvider ctx.protocol bs a parseGas outF)
    (hBudget : ProviderModelBudget cfg size raw modelSt ctx S a parseGas outF)
    (hentry : CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
    (hag : CopiedAgreement cfg ctx raw modelSt a tr (erase (hostOf ctx raw)))
    (hagP : CopiedAgreement cfg ctx raw modelSt a tr (eraseP (hostOf ctx raw))) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact method_refines_callR (WNear.wnear cfg) size codeOf raw modelSt ctx (.ftBalanceOf a)
    (CopiedAbsentPre S a bs tr bud) (providerMethodCost ctx.protocol S a parseGas outF) (copiedMethodPost a tr)
    hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_297) funcType_297 (by decide) (by decide)
    (provider_absent_runs ctx.protocol S a bs parseGas outF tr bud hlen hpos hProvider)
    hentry.1 hentry.2
    (fun e he => copied_post_noPromises (e := erase (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    (fun e he => copied_post_noPromises (e := eraseP (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    hag hagP hBudget

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_absent_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8) (parseGas outF : Nat)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hlen : bs.length < 2 ^ 24)
    (hpos : 0 < bs.length)
    (hProvider : DeployedParserProvider ctx.protocol bs a parseGas outF)
    (hBudget : ProviderModelBudget cfg size raw (some S) ctx S a parseGas outF)
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
  obtain ⟨hinv, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  have hkey := NearDepositMethod.accountKey_ofNear a.toNear
  simp only [WNear.AccountId.ofNear_toNear] at hkey
  change WNear.accountKey a = WNear.accountsPrefix ++
    (bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList) at hkey
  rw [Wasm.ByteEncoding.string_utf8_length] at hkey
  have hnone : (hostOf ctx raw).storage (copiedKey a) = none := by
    have hr := FtBalanceOfMethod.reg_storage ctx raw S hwf hraw (hostOf ctx raw) rfl a
    rw [hkey] at hr
    simpa only [NearDepositMethod.regOf, if_neg ha, Option.map_none] using hr
  have hentry := copied_entry_at_of_ctx cfg ctx raw (some S) S a bs hwf hl hargs hlen hval hnone
  exact provider_absent_refines_with_obligations cfg size codeOf raw (some S) ctx S a bs parseGas outF
    ctx.trie (WNear.proofBound ctx) hp hwf hm hlen hpos hProvider hBudget hentry
    (copied_agreement_of_represents cfg ctx raw (some S) S a ctx.trie hrep hwf hentry.2.value hentry.2.absent _ rfl)
    (copied_agreement_of_represents cfg ctx raw (some S) S a ctx.trie hrep hwf hentry.2.value hentry.2.absent _ rfl)

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open NearInterface ContractModel in
/-- A shared witness ties the actual successful parser's gas/heap bounds to the unchanged receipt budget. -/
noncomputable def AbsentParserPlan (cfg : WNear.Config) (size : Nat) (raw : RawStorage)
    (modelSt : Option WNear.State) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (bs : List UInt8) : Prop :=
  ∃ parseGas outF, bs.length < 2 ^ 24 ∧ 0 < bs.length ∧
    DeployedParserProvider ctx.protocol bs a parseGas outF ∧
    ProviderModelBudget cfg size raw modelSt ctx S a parseGas outF

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_plan_refines_with_obligations (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of")
    (hPlan : AbsentParserPlan cfg size raw modelSt ctx S a bs)
    (hentry : CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
    (hag : CopiedAgreement cfg ctx raw modelSt a tr (erase (hostOf ctx raw)))
    (hagP : CopiedAgreement cfg ctx raw modelSt a tr (eraseP (hostOf ctx raw))) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨parseGas, outF, hlen, hpos, hProvider, hBudget⟩ := hPlan
  exact provider_absent_refines_with_obligations cfg size codeOf raw modelSt ctx S a bs parseGas outF tr bud
    hp hwf hm hlen hpos hProvider hBudget hentry hag hagP

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_plan_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hPlan : AbsentParserPlan cfg size raw (some S) ctx S a bs)
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
  obtain ⟨parseGas, outF, hlen, hpos, hProvider, hBudget⟩ := hPlan
  exact provider_absent_refines_init cfg size codeOf raw ctx S a bs parseGas outF
    hp hwf hm hl hlen hpos hProvider hBudget hargs hrep ha

end WNear.Binary.BalanceOf297AbsentCall
