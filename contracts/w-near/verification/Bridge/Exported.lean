import Spec.Contract
import Spec.Exports
import Bridge.Methods.FtTotalSupplyAll
import Bridge.Methods.StorageMinimumBalanceRefines
import Bridge.Methods.StorageBalanceBoundsRefines
import Bridge.Methods.FtMetadataRefines
import Bridge.Methods.NewRefines
import Bridge.Methods.NearDepositAll

/-! # Checked exported-method composition and named remaining verification obligations -/
namespace WNear.Binary.Exported
open Wasm Wasm.Near NearInterface

/-- Exactly the deployed refinement clauses at one represented call context. -/
def At (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) : Prop :=
  let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
  (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
  (∀ c, (wnear cfg).Parses ctx.method ctx.args c →
    let res := (wnear cfg).step ctx st c
    ((wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c) →
      Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
    (Matches (wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs))) ∧
  ((¬ ∃ c, (wnear cfg).Parses ctx.method ctx.args c) → RolledBack ctx raw r)

/-- The full obligation for a named method, including invalid arguments and every resource state. -/
def MethodClause (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (method : String) : Prop :=
  cfg.WF → ∀ (raw : RawStorage) (st : Option WNear.State) (ctx : Context),
    (wnear cfg).Represents raw st → ctx.WF raw → ctx.protocol = protocol → ctx.method = method →
    At cfg size codeOf raw st ctx

/-- Exact interface consumed by the global refinement composition.
A witness must cover every exported method, including rejected input and all resources. -/
def Clauses (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) : Prop :=
  ∀ method, method ∈ exportedMethods → MethodClause cfg size codeOf protocol method

/-- Reviewed environmental premises; their instantiation from the pinned JSON remains an obligation. -/
structure Environment (protocol : RuntimeConfig) : Prop where
  runtime : WProtocol protocol
  costs : FtTotalSupplyMethod.CostsV86 protocol
  limits : FtTotalSupplyMethod.LimitsV86 protocol
  newCosts : NewMethod.CostsNewV86 protocol
  depositCosts : NearDepositGas.CostsDepositV86 protocol

/-- Each field is a separate unproved method contract, not an assumption hidden inside a completed result. -/
structure Remaining (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) : Prop where
  nearWithdraw : MethodClause cfg size codeOf protocol "near_withdraw"
  ftTransfer : MethodClause cfg size codeOf protocol "ft_transfer"
  ftTransferCall : MethodClause cfg size codeOf protocol "ft_transfer_call"
  ftBalanceOf : MethodClause cfg size codeOf protocol "ft_balance_of"
  ftResolveTransfer : MethodClause cfg size codeOf protocol "ft_resolve_transfer"
  storageDeposit : MethodClause cfg size codeOf protocol "storage_deposit"
  storageWithdraw : MethodClause cfg size codeOf protocol "storage_withdraw"
  storageUnregister : MethodClause cfg size codeOf protocol "storage_unregister"
  storageBalanceOf : MethodClause cfg size codeOf protocol "storage_balance_of"

/-- Unit-argument methods have no rejecting argument branch; their complete call proof supplies every clause. -/
theorem unit_at (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c0 : WNear.Call)
    (hdecode : WNear.Call.decode ctx.method ctx.args = some c0)
    (hcall : let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
      let res := (wnear cfg).step ctx st c0
      (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
      ((wnear cfg).gas ctx st c0 ≤ ctx.gasLimit → ctx.ProofRoom ((wnear cfg).proofBound ctx st c0) →
        Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c0) ∧
      (Matches (wnear cfg) ctx raw r res ∨
        (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs))) :
    At cfg size codeOf raw st ctx := by
  obtain ⟨hni, hgas, hany⟩ := hcall
  refine ⟨hni, ?_, ?_⟩
  · intro c hc
    change WNear.Call.decode ctx.method ctx.args = some c at hc
    have he := Option.some.inj (hc.symm.trans hdecode)
    subst he
    exact ⟨hgas, hany⟩
  · intro hn
    exact (hn ⟨c0, hdecode⟩).elim

/-- Integrated full method clause, under the reviewed environmental premises. -/
theorem ftTotalSupply_complete (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625) :
    MethodClause cfg size codeOf protocol "ft_total_supply" := by
  intro hcfg raw st ctx hrep hwf hprot hm
  subst protocol
  apply unit_at cfg size codeOf raw st ctx .ftTotalSupply
  · simp only [hm, WNear.Call.decode]
  · exact FtTotalSupplyMethod.ftTotalSupply_refines_all cfg size codeOf raw st ctx he.runtime hwf hrep hm he.costs he.limits hsize

/-- Integrated full method clause, under the reviewed environmental premises. -/
theorem storageMinimumBalance_complete (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625) :
    MethodClause cfg size codeOf protocol "storage_minimum_balance" := by
  intro hcfg raw st ctx hrep hwf hprot hm
  subst protocol
  apply unit_at cfg size codeOf raw st ctx .storageMinimumBalance
  · simp only [hm, WNear.Call.decode]
  · exact StorageMinimumBalanceMethod.storageMinimumBalance_refines_all cfg size codeOf raw st ctx he.runtime hwf hrep hm he.costs he.limits hsize

/-- Integrated full method clause, under the reviewed environmental premises. -/
theorem storageBalanceBounds_complete (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625) :
    MethodClause cfg size codeOf protocol "storage_balance_bounds" := by
  intro hcfg raw st ctx hrep hwf hprot hm
  subst protocol
  apply unit_at cfg size codeOf raw st ctx .storageBalanceBounds
  · simp only [hm, WNear.Call.decode]
  · exact StorageBalanceBoundsMethod.storageBalanceBounds_refines_all cfg size codeOf raw st ctx he.runtime hwf hrep hm he.costs he.limits hsize

/-- Integrated full method clause, under the reviewed environmental premises. -/
theorem ftMetadata_complete (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625) :
    MethodClause cfg size codeOf protocol "ft_metadata" := by
  intro hcfg raw st ctx hrep hwf hprot hm
  subst protocol
  apply unit_at cfg size codeOf raw st ctx .ftMetadata
  · simp only [hm, WNear.Call.decode]
  · exact FtMetadataMethod.ftMetadata_refines_all cfg size codeOf raw st ctx he.runtime hwf hrep hm he.costs he.limits hsize

/-- Integrated full method clause, under the reviewed environmental premises. -/
theorem new_complete (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625) :
    MethodClause cfg size codeOf protocol "new" := by
  intro hcfg raw st ctx hrep hwf hprot hm
  subst protocol
  apply unit_at cfg size codeOf raw st ctx .new
  · simp only [hm, WNear.Call.decode]
  · exact NewMethod.newRefines_all cfg size codeOf raw st ctx he.runtime hwf hrep hm he.costs he.newCosts he.limits hsize

/-- Integrated full method clause, under the reviewed environmental premises. -/
theorem nearDeposit_complete (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625) :
    MethodClause cfg size codeOf protocol "near_deposit" := by
  intro hcfg raw st ctx hrep hwf hprot hm
  subst protocol
  apply unit_at cfg size codeOf raw st ctx .nearDeposit
  · simp only [hm, WNear.Call.decode]
  · exact NearDepositMethod.nearDeposit_refines_all cfg size codeOf raw st ctx he.runtime hwf hrep hm he.costs he.limits he.depositCosts hsize

/-- Checked dispatch over all fifteen exports; named remaining contracts stay explicit hypotheses. -/
theorem all_methods (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625)
    (hr : Remaining cfg size codeOf protocol) (method : String) (hm : method ∈ exportedMethods) :
    MethodClause cfg size codeOf protocol method := by
  simp only [exportedMethods, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact storageMinimumBalance_complete cfg size codeOf protocol he hsize
  · exact nearDeposit_complete cfg size codeOf protocol he hsize
  · exact hr.nearWithdraw
  · exact new_complete cfg size codeOf protocol he hsize
  · exact hr.ftTransfer
  · exact hr.ftTransferCall
  · exact ftTotalSupply_complete cfg size codeOf protocol he hsize
  · exact hr.ftBalanceOf
  · exact hr.ftResolveTransfer
  · exact hr.storageDeposit
  · exact hr.storageWithdraw
  · exact hr.storageUnregister
  · exact storageBalanceBounds_complete cfg size codeOf protocol he hsize
  · exact hr.storageBalanceOf
  · exact ftMetadata_complete cfg size codeOf protocol he hsize

/-- Admission-free assembly of the exported interface from completed methods and named obligations. -/
theorem all_clauses (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : RuntimeConfig) (he : Environment protocol) (hsize : size ≤ 185625)
    (hr : Remaining cfg size codeOf protocol) : Clauses cfg size codeOf protocol :=
  all_methods cfg size codeOf protocol he hsize hr

end WNear.Binary.Exported
