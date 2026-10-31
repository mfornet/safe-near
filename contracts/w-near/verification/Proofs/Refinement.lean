import Bridge.Methods.FtBalanceOfSmallGeneralObject
import Bridge.Methods.AcceptedInputBounds
import Bridge.Methods.FtBalanceOfProviderRefines
import Spec.Contract
import Bridge.Exported
import Bridge.Methods.FtBalanceOfCopiedCase
import Bridge.Methods.FtBalanceOfArrayCase
import Bridge.Methods.FtBalanceOfObjectCase
import Spec.Exports
import Binary.Module
import Proofs.Availability
import NearRuntime.BoundaryResolution
import Lean
import Wasm.Binary

/-!
# The refinement obligation (open)

`Spec/Contract.lean` gives the wNEAR `ContractModel`; `NearRuntime.Boundary`
gives near-lean's `RuntimeInterface`, a function-call action followed by the
receipt's storage-stake check. This file pins the deployed binary and the
protocol configuration, so that `refines_wnear` below is a closed statement
about `contract.wasm` under that configuration.

The binary is `Binary.wNearBytes`, the bytes of `../contract.wasm` read when
`Binary/Bytes.lean` is elaborated (the adapter tests check that they are the
file's). `Binary.decode_wNearBytes` proves in the kernel what they decode
to, so the facts the statement needs about the module (no start function;
the exported functions) are theorems here, not hypotheses.

The protocol configuration is pinned the same way: the JSON of the latest
config in `near-lean/vm/configs`, the one the adapter tests run on, is
embedded, and the parsed configuration is a hypothesis. Gas costs and limits
are protocol parameters: `gasBound` is a sum of constants measured under this
configuration, and the binary's logs and register reads succeed only under
its limits, so the statement does not hold for every configuration.

`refines_wnear_exported` composes six completed method clauses with nine named
remaining method obligations and five pinned-protocol obligations. The global
results remain incomplete through these explicit leaves. The audit remains
strict outside this frontier and checks its exact admitted declarations.
-/

namespace WNear

open NearInterface
open Binary (wNearBytes wNearModule decode_wNearBytes)

open Lean Elab Term in
/-- The text of a file, as a string literal, read when this file is
elaborated. Paths are relative to the package root. -/
elab "file_text%" path:str : term => do
  return mkStrLit (← IO.FS.readFile path.getString)

/-- The protocol version the statement is pinned to. -/
def wNearProtocolVersion : Nat := 86

/-- The pinned version is the latest config, the one the adapter tests load:
a new config breaks this until the statement is re-pinned. -/
example : wNearProtocolVersion = Wasm.Near.RuntimeConfig.latestVersion := rfl

/-- `runtime_config_v86.json`, nearcore's `RuntimeConfigView` at version 86. -/
def wNearProtocolJson : String := file_text% "../../../near-lean/vm/configs/runtime_config_v86.json"

/-- The module the binary decodes to. -/
theorem code_eq {code : Wasm.Module} (hcode : Wasm.Binary.decode wNearBytes = .ok code) :
    code = wNearModule := by
  rw [decode_wNearBytes] at hcode
  exact (Except.ok.inj hcode).symm

/-- The binary has no start function. -/
theorem start_wNearModule : wNearModule.start = none := rfl

/-- The binary exports exactly the methods `Call.decode` knows, as functions. -/
theorem exports_wNearModule : funcExportNames wNearModule = exportedMethods := by decide +kernel

theorem exportFunc_none {m : Wasm.Module} {name : String} (h : name ∉ funcExportNames m) :
    m.exportFunc? name = none := by
  unfold Wasm.Module.exportFunc?
  rw [← Array.findSome?_toList, List.findSome?_eq_none_iff]
  intro e he
  split
  · rename_i i hd
    split
    · rename_i hn
      exact absurd (List.mem_filterMap.mpr ⟨e, he, by simp [hd, beq_iff_eq.mp hn]⟩) h
    · rfl
  · rfl

/-- Methods the binary does not export are no calls. -/
theorem decode_not_exported {method : String} (h : method ∉ exportedMethods) (args : List UInt8) :
    Call.decode method args = none := by
  simp only [exportedMethods, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold Call.decode
  split <;> simp_all

/-- The pinned configuration must actually parse before the conditional refinement can be instantiated. -/
def PinnedProtocolAvailable : Prop :=
  ∃ protocol, Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol

/-- Kernel-checked size of the exact embedded deployed binary. -/
theorem deployed_code_size : wNearBytes.size ≤ 185625 := by
  rw [Binary.wNearBytes, Wasm.ByteSource.size_toBytes]
  decide +kernel

/-- Open protocol-86 verification obligation; not an established environmental fact. -/
theorem pinned_runtime_obligation (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol) :
    Binary.WProtocol protocol := by
  sorry

/-- Open protocol-86 verification obligation; not an established environmental fact. -/
theorem pinned_costs_obligation (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol) :
    Binary.FtTotalSupplyMethod.CostsV86 protocol := by
  sorry

/-- Open protocol-86 verification obligation; not an established environmental fact. -/
theorem pinned_limits_obligation (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol) :
    Binary.FtTotalSupplyMethod.LimitsV86 protocol := by
  sorry

/-- Open protocol-86 verification obligation; not an established environmental fact. -/
theorem pinned_new_costs_obligation (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol) :
    Binary.NewMethod.CostsNewV86 protocol := by
  sorry

/-- Open protocol-86 verification obligation; not an established environmental fact. -/
theorem pinned_deposit_costs_obligation (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol) :
    Binary.NearDepositGas.CostsDepositV86 protocol := by
  sorry

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem nearWithdraw_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "near_withdraw" := by
  sorry

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem ftTransfer_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "ft_transfer" := by
  sorry

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem ftTransferCall_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "ft_transfer_call" := by
  sorry

/-- Exact remaining pinned-JSON argument ceiling; no protocol parse witness is supplied here. -/
theorem pinned_arguments_obligation (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol) :
    Binary.InputDomain.ArgumentLimitV86 protocol := by
  sorry

/-- Precise remaining parser/resource/gas obligation outside completed array, escape-free object,
and <=10000-byte general-object cases. No full-domain gas or parser result is assumed proved. -/
theorem ftBalanceOf_absent_parser_complement_obligation (cfg : Config)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (ctx : Context) (S : State) (a : AccountId)
    (hrep : (wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hparse : (wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a)) (ha : a ∉ S.registered)
    (hother : ¬ Binary.BalanceOf297AbsentCall.ArrayAbsentCase (some S) ctx (.ftBalanceOf a))
    (hobject : ¬ Binary.BalanceOf297AbsentCall.ObjectAbsentCase (some S) ctx (.ftBalanceOf a))
    (hsmall : ¬ Binary.BalanceOf297AbsentCall.SmallGeneralObjectAbsentCase (some S) ctx (.ftBalanceOf a)) :
    ∃ parseGas outF, Binary.BalanceOf297AbsentCall.DeployedParserProvider ctx.protocol ctx.args a parseGas outF ∧
      Binary.BalanceOf297AbsentCall.ProviderModelBudget cfg wNearBytes.size raw (some S) ctx S a parseGas outF := by
  sorry

/-- Checked split: the actual small general-object parser and original budget are constructed;
only the explicitly complementary accepted initialized/absent inputs remain admitted. -/
theorem ftBalanceOf_absent_parser_cost_obligation (cfg : Config)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (ctx : Context) (S : State) (a : AccountId)
    (hrep : (wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hparse : (wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a)) (ha : a ∉ S.registered)
    (hother : ¬ Binary.BalanceOf297AbsentCall.ArrayAbsentCase (some S) ctx (.ftBalanceOf a))
    (hobject : ¬ Binary.BalanceOf297AbsentCall.ObjectAbsentCase (some S) ctx (.ftBalanceOf a)) :
    ∃ parseGas outF, Binary.BalanceOf297AbsentCall.DeployedParserProvider ctx.protocol ctx.args a parseGas outF ∧
      Binary.BalanceOf297AbsentCall.ProviderModelBudget cfg wNearBytes.size raw (some S) ctx S a parseGas outF := by
  classical
  by_cases hsmall : Binary.BalanceOf297AbsentCall.SmallGeneralObjectAbsentCase (some S) ctx (.ftBalanceOf a)
  · exact Binary.BalanceOf297AbsentCall.small_general_parser_cost cfg wNearBytes.size raw ctx S a
      (hctx ▸ he.costs) deployed_code_size hrep hwf hsmall
  · exact ftBalanceOf_absent_parser_complement_obligation cfg protocol hprotocol he hcfg raw ctx S a
      hrep hwf hctx hm hparse ha hother hobject hsmall

/-- Checked construction: accepted-input nonemptiness is proved, and the protocol ceiling and parser cost remain explicit. -/
theorem ftBalanceOf_absent_parser_plan_obligation (cfg : Config)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (ctx : Context) (S : State) (a : AccountId)
    (hrep : (wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hparse : (wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a)) (ha : a ∉ S.registered)
    (hother : ¬ Binary.BalanceOf297AbsentCall.ArrayAbsentCase (some S) ctx (.ftBalanceOf a))
    (hobject : ¬ Binary.BalanceOf297AbsentCall.ObjectAbsentCase (some S) ctx (.ftBalanceOf a)) :
    Binary.BalanceOf297AbsentCall.AbsentParserPlan cfg wNearBytes.size raw (some S) ctx S a ctx.args := by
  have hlimit : Binary.InputDomain.ArgumentLimitV86 ctx.protocol :=
    hctx ▸ pinned_arguments_obligation protocol hprotocol
  exact Binary.BalanceOf297AbsentCall.absent_plan_of_parser_cost cfg wNearBytes.size raw (some S) ctx S a
    hwf hm hparse hlimit
    (ftBalanceOf_absent_parser_cost_obligation cfg protocol hprotocol he hcfg raw ctx S a hrep hwf hctx hm hparse ha hother hobject)

/-- Remaining safety contexts outside the completed array and escape-free object cases. -/
theorem ftBalanceOf_other_input_state_no_issue_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hother : ¬ ∃ c, Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c)
    (hobject : ¬ ∃ c, Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c)
    (hstate : ¬ ∃ (S : State) (a : AccountId), st = some S ∧ (wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a) ∧ a ∉ S.registered) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  sorry

/-- Checked split through actual-code parser/resource/gas composition; precise complementary states remain Open. -/
theorem ftBalanceOf_outside_array_object_absent_no_issue_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hother : ¬ ∃ c, Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c)
    (hobject : ¬ ∃ c, Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  classical
  by_cases hsmall : ∃ c, Binary.BalanceOf297AbsentCall.SmallGeneralObjectAbsentCase st ctx c
  · obtain ⟨c, hc⟩ := hsmall
    exact Binary.BalanceOf297AbsentCall.small_general_object_case_no_issue cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hc
  ·
    by_cases hcase : ∃ (S : State) (a : AccountId), st = some S ∧ (wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a) ∧ a ∉ S.registered
    · obtain ⟨S, a, rfl, hparse, ha⟩ := hcase
      have hPlan := ftBalanceOf_absent_parser_plan_obligation cfg protocol hprotocol he hcfg raw ctx S a
        hrep hwf hctx hm hparse ha (fun hx => hother ⟨_, hx⟩) (fun hx => hobject ⟨_, hx⟩)
      exact (Binary.BalanceOf297AbsentCall.provider_plan_refines_init cfg wNearBytes.size codeOf raw ctx S a ctx.args
        (hctx ▸ he.runtime) hwf hm (hctx ▸ he.limits) hPlan rfl hrep ha).1
    · exact ftBalanceOf_other_input_state_no_issue_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm hother hobject hcase

/-- Checked split on the completed escape-free object case; the precise complement remains Open. -/
theorem ftBalanceOf_outside_array_absent_no_issue_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hother : ¬ ∃ c, Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  classical
  by_cases hcase : ∃ c, Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c
  · obtain ⟨c, hcase⟩ := hcase
    exact Binary.BalanceOf297AbsentCall.object_case_no_issue cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hcase
  · exact ftBalanceOf_outside_array_object_absent_no_issue_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm hother hcase

/-- Checked extension of the remaining copied-only case to all valid strings in this array branch. -/
theorem ftBalanceOf_other_no_issue_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hother : ¬ ∃ c, Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  classical
  by_cases hcase : ∃ c, Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c
  · obtain ⟨c, hcase⟩ := hcase
    exact Binary.BalanceOf297AbsentCall.array_case_no_issue cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hcase
  · exact ftBalanceOf_outside_array_absent_no_issue_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm hcase

/-- Execution safety for every represented `ft_balance_of` context, including rejected input. -/
theorem ftBalanceOf_no_issue_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of") :
    ∀ msg, (Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  classical
  by_cases hcase : ∃ c, Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c
  · obtain ⟨c, hcase⟩ := hcase
    exact Binary.BalanceOf297AbsentCall.copied_case_no_issue cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hcase
  · exact ftBalanceOf_other_no_issue_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx
      hrep hwf hctx hm hcase

/-- Remaining accepted inputs and states outside the completed array and escape-free object cases. -/
theorem ftBalanceOf_other_state_accepted_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (c : Call) (hparse : (wnear cfg).Parses ctx.method ctx.args c)
    (hother : ¬ Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c)
    (hobject : ¬ Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c)
    (hstate : ¬ ∃ (S : State) (a : AccountId), st = some S ∧ c = .ftBalanceOf a ∧ a ∉ S.registered) :
    let r := Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx
    let res := (wnear cfg).step ctx st c
    ((wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c) →
      Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
    (Matches (wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  sorry

/-- Checked split through actual-code parser/resource/gas composition; precise complementary states remain Open. -/
theorem ftBalanceOf_outside_array_object_absent_accepted_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (c : Call) (hparse : (wnear cfg).Parses ctx.method ctx.args c)
    (hother : ¬ Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c)
    (hobject : ¬ Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx
    let res := (wnear cfg).step ctx st c
    ((wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c) →
      Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
    (Matches (wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  classical
  by_cases hsmall : Binary.BalanceOf297AbsentCall.SmallGeneralObjectAbsentCase st ctx c
  · exact Binary.BalanceOf297AbsentCall.small_general_object_case_accepted cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hsmall
  ·
    by_cases hcase : ∃ (S : State) (a : AccountId), st = some S ∧ c = .ftBalanceOf a ∧ a ∉ S.registered
    · obtain ⟨S, a, rfl, rfl, ha⟩ := hcase
      have hPlan := ftBalanceOf_absent_parser_plan_obligation cfg protocol hprotocol he hcfg raw ctx S a
        hrep hwf hctx hm hparse ha hother hobject
      exact (Binary.BalanceOf297AbsentCall.provider_plan_refines_init cfg wNearBytes.size codeOf raw ctx S a ctx.args
        (hctx ▸ he.runtime) hwf hm (hctx ▸ he.limits) hPlan rfl hrep ha).2
    · exact ftBalanceOf_other_state_accepted_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm c hparse hother hobject hcase

/-- Checked split on the completed escape-free object case; the precise complement remains Open. -/
theorem ftBalanceOf_outside_array_absent_accepted_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (c : Call) (hparse : (wnear cfg).Parses ctx.method ctx.args c)
    (hother : ¬ Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx
    let res := (wnear cfg).step ctx st c
    ((wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c) →
      Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
    (Matches (wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  classical
  by_cases hcase : Binary.BalanceOf297AbsentCall.ObjectAbsentCase st ctx c
  · exact Binary.BalanceOf297AbsentCall.object_case_accepted cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hcase
  · exact ftBalanceOf_outside_array_object_absent_accepted_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm c hparse hother hcase

/-- Checked extension of the remaining copied-only case to all valid strings in this array branch. -/
theorem ftBalanceOf_other_accepted_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (c : Call) (hparse : (wnear cfg).Parses ctx.method ctx.args c)
    (hother : ¬ Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx
    let res := (wnear cfg).step ctx st c
    ((wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c) →
      Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
    (Matches (wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  classical
  by_cases hcase : Binary.BalanceOf297AbsentCall.ArrayAbsentCase st ctx c
  · exact Binary.BalanceOf297AbsentCall.array_case_accepted cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hcase
  · exact ftBalanceOf_outside_array_absent_accepted_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm c hparse hcase

/-- Accepted calls satisfy both resource-sufficient refinement and arbitrary-resource rollback clauses. -/
theorem ftBalanceOf_accepted_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (c : Call) (hparse : (wnear cfg).Parses ctx.method ctx.args c) :
    let r := Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx
    let res := (wnear cfg).step ctx st c
    ((wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c) →
      Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
    (Matches (wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  classical
  by_cases hcase : Binary.BalanceOf297AbsentCall.CopiedAbsentCase st ctx c
  · exact Binary.BalanceOf297AbsentCall.copied_case_accepted cfg wNearBytes.size codeOf protocol he
      deployed_code_size raw st ctx c hrep hwf hctx hm hcase
  · exact ftBalanceOf_other_accepted_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx
      hrep hwf hctx hm c hparse hcase

/-- Rejected arguments must leave the represented state rolled back. -/
theorem ftBalanceOf_rejected_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) (hcfg : cfg.WF)
    (raw : RawStorage) (st : Option State) (ctx : Context)
    (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hreject : ¬ ∃ c, (wnear cfg).Parses ctx.method ctx.args c) :
    RolledBack ctx raw (Near.Boundary.nearRuntime.exec (Binary.wCode wNearBytes.size codeOf) raw ctx) := by
  sorry

/-- Checked assembly of the unchanged full method clause from its three exact branches. -/
theorem ftBalanceOf_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "ft_balance_of" := by
  intro hcfg raw st ctx hrep hwf hctx hm
  refine ⟨ftBalanceOf_no_issue_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm, ?_, ?_⟩
  · intro c hparse
    exact ftBalanceOf_accepted_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm c hparse
  · intro hreject
    exact ftBalanceOf_rejected_obligation cfg codeOf protocol hprotocol he hcfg raw st ctx hrep hwf hctx hm hreject

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem ftResolveTransfer_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "ft_resolve_transfer" := by
  sorry

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem storageDeposit_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "storage_deposit" := by
  sorry

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem storageWithdraw_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "storage_withdraw" := by
  sorry

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem storageUnregister_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "storage_unregister" := by
  sorry

/-- Open full method obligation, including rejected arguments and arbitrary represented resource states. -/
theorem storageBalanceOf_obligation (cfg : Config) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (he : Binary.Exported.Environment protocol) :
    Binary.Exported.MethodClause cfg wNearBytes.size codeOf protocol "storage_balance_of" := by
  sorry

/-- **Conditional composition.** The exported methods: on a call to one of them under the pinned
protocol configuration, near-lean's execution of `contract.wasm` is the
model's as `Refines` states it. -/
theorem refines_wnear_exported (cfg : Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (raw : RawStorage) (st : Option State) (ctx : Context) (hrep : (wnear cfg).Represents raw st)
    (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) (hmethod : ctx.method ∈ exportedMethods) :
    let r := Near.Boundary.nearRuntime.exec
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (∀ c, (wnear cfg).Parses ctx.method ctx.args c →
      let res := (wnear cfg).step ctx st c
      ((wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c) →
        Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
      (Matches (wnear cfg) ctx raw r res ∨
        (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs))) ∧
    ((¬ ∃ c, (wnear cfg).Parses ctx.method ctx.args c) → RolledBack ctx raw r) := by
  have hsame := code_eq hcode
  subst code
  have he : Binary.Exported.Environment protocol :=
    ⟨pinned_runtime_obligation protocol hprotocol,
      pinned_costs_obligation protocol hprotocol,
      pinned_limits_obligation protocol hprotocol,
      pinned_new_costs_obligation protocol hprotocol,
      pinned_deposit_costs_obligation protocol hprotocol⟩
  have hr : Binary.Exported.Remaining cfg wNearBytes.size codeOf protocol :=
    {
      nearWithdraw := nearWithdraw_obligation cfg codeOf protocol hprotocol he,
      ftTransfer := ftTransfer_obligation cfg codeOf protocol hprotocol he,
      ftTransferCall := ftTransferCall_obligation cfg codeOf protocol hprotocol he,
      ftBalanceOf := ftBalanceOf_obligation cfg codeOf protocol hprotocol he,
      ftResolveTransfer := ftResolveTransfer_obligation cfg codeOf protocol hprotocol he,
      storageDeposit := storageDeposit_obligation cfg codeOf protocol hprotocol he,
      storageWithdraw := storageWithdraw_obligation cfg codeOf protocol hprotocol he,
      storageUnregister := storageUnregister_obligation cfg codeOf protocol hprotocol he,
      storageBalanceOf := storageBalanceOf_obligation cfg codeOf protocol hprotocol he }
  exact Binary.Exported.all_methods cfg wNearBytes.size codeOf protocol he deployed_code_size hr
    ctx.method hmethod hcfg raw st ctx hrep hwf hprot rfl

/-- Admission-free global composition. The exported interface is an unresolved
verification dependency until its exact method clauses are instantiated. The
non-exported branch is discharged by binary export facts and boundary rollback. -/
theorem refines_wnear_of_clauses (cfg : Config) (code : Wasm.Module)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (hc : Binary.Exported.Clauses cfg wNearBytes.size codeOf protocol) :
    Refines Near.Boundary.nearRuntime protocol
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } (wnear cfg) := by
  intro raw st ctx hrep hwf hprot
  have hstart : code.start = none := code_eq hcode ▸ start_wNearModule
  have hexports : funcExportNames code = exportedMethods := code_eq hcode ▸ exports_wNearModule
  by_cases hmethod : ctx.method ∈ exportedMethods
  · have hsame := code_eq hcode
    subst code
    exact hc ctx.method hmethod hcfg raw st ctx hrep hwf hprot rfl
  · have hexport : code.exportFunc? ctx.method = none := exportFunc_none (by rw [hexports]; exact hmethod)
    obtain ⟨hrb, hni⟩ := Near.Boundary.nearRuntime_not_exported
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } raw ctx rfl
      hstart hexport
    have hnone : ∀ c, ¬ (wnear cfg).Parses ctx.method ctx.args c := by
      intro c hc
      change Call.decode ctx.method ctx.args = some c at hc
      rw [decode_not_exported hmethod] at hc
      cases hc
    exact ⟨hni, fun c hc => absurd hc (hnone c), fun _ => hrb⟩

/-- Admission-free route from the reviewed environment and nine named remaining
method obligations to the unchanged deployed-binary refinement. No protocol parse
witness or method proof is supplied by this theorem. -/
theorem refines_wnear_with_obligations (cfg : Config) (code : Wasm.Module)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (he : Binary.Exported.Environment protocol)
    (hr : Binary.Exported.Remaining cfg wNearBytes.size codeOf protocol) :
    Refines Near.Boundary.nearRuntime protocol
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } (wnear cfg) :=
  refines_wnear_of_clauses cfg code codeOf protocol hcfg hcode
    (Binary.Exported.all_clauses cfg wNearBytes.size codeOf protocol he deployed_code_size hr)

/-- The deployed wNEAR binary refines the model: for every configuration whose
measured account entry fits a `u64`, every context under the pinned protocol
configuration (version 86) and every resource state, near-lean's execution of
`contract.wasm` is the model's as `Refines` states it. `codeOf` decodes code that the call's promises deploy; wNEAR deploys none.
Proved for every method the binary does not export; conditional for the exported
ones on the named method and protocol obligations. -/
@[blueprint "spec:refinement"
  (statement := /-- The deployed binary refines \cref{def:contract-model} under the pinned protocol configuration (version 86): for every storage representing a model state and every context the runtime can build with that configuration, the execution reports no interpreter limitation; with at least the model's gas bound attached, it agrees with the model on return value, storage, balance, storage usage, logs, receipts and failure, and uses at most that much gas; with less, it agrees or fails for gas with no effects; and input that is no call fails with no effects. -/)
  (notReady := true)]
theorem refines_wnear (cfg : Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol) :
    Refines Near.Boundary.nearRuntime protocol
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } (wnear cfg) := by
  apply refines_wnear_of_clauses cfg code codeOf protocol hcfg hcode
  intro method hmethod hcfg' raw st ctx hrep hwf hprot hm
  have hcall := refines_wnear_exported cfg code codeOf protocol hcfg' hcode hprotocol
    raw st ctx hrep hwf hprot (hm ▸ hmethod)
  have hsame := code_eq hcode
  subst code
  exact hcall

/-- `withdraw_available_binary` for `contract.wasm` on near-lean under the
pinned protocol configuration: a withdrawal attached with at least the model's gas bound succeeds on the deployed binary.
It depends on `refines_wnear`, which a withdrawal reaches through the conditional
`refines_wnear_exported`, so the audit lists its unresolved dependencies too. -/
theorem withdraw_available_wasm (cfg : Config) (code : Wasm.Module)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    {s : State} {ctx : Context} {amount : Nat}
    (hs : Inv cfg s) (hwf : ctx.WF (encode s)) (hprot : ctx.protocol = protocol)
    (hparse : Parses ctx.method ctx.args (.nearWithdraw amount))
    (hreg : AccountId.ofNear ctx.predecessor ∈ s.registered)
    (hamt : amount ≤ s.balance (AccountId.ofNear ctx.predecessor)) (hdep : ctx.attached = 1)
    (hbound : amount + 1 < u128Bound) (hbal : amount ≤ ctx.balance)
    (hrent : stakeDeficit ctx.protocol (usageAfter ctx (some s)
      { s.setBalance (AccountId.ofNear ctx.predecessor)
          (s.balance (AccountId.ofNear ctx.predecessor) - amount) with
        totalSupply := s.totalSupply - amount }) (ctx.balance - amount) ctx.locked = 0)
    (hlog : logLimitError ctx.protocol
      [s!"Withdraw {amount} NEAR from {AccountId.ofNear ctx.predecessor}"] = none)
    (hreceipts : ReceiptValidation.callReceiptsError ctx.protocol ctx.current ctx.signer ctx.signerPk
      (encodeReceipts [.transfer (AccountId.ofNear ctx.predecessor) (amount + 1)]) = none)
    (hgas : gasBound ctx (.nearWithdraw amount) ≤ ctx.gasLimit)
    (hproof : ctx.ProofRoom (proofBound ctx)) :
    let r := Near.Boundary.nearRuntime.exec
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } (encode s) ctx
    r.outcome = .ok (.receiptIndex 0) ∧
      r.storage =
        encode { s.setBalance (AccountId.ofNear ctx.predecessor)
            (s.balance (AccountId.ofNear ctx.predecessor) - amount) with
          totalSupply := s.totalSupply - amount } :=
  withdraw_available_binary (refines_wnear cfg code codeOf protocol hcfg hcode hprotocol)
    hs hwf hprot hparse hreg hamt hdep hbound hbal hrent hlog hreceipts hgas hproof

end WNear
