import NearInterface.Model

/-!
# Refinement of a binary by a contract model

`Refines R protocol code M` characterises every execution of `code` under the
runtime `R` and the protocol configuration `protocol`: every input, every
amount of attached gas, every resource state the runtime can produce. The
only hypotheses are that the storage represents a model state, that the
context is one the runtime builds (`Context.WF`), and that it carries
`protocol`. Gas costs and limits are protocol parameters, so a model's gas
bound and its panic-free paths hold for given configurations, not for all.

* With at least `M.gas` gas, the execution is the model's, and uses at most
  that much gas.
* With less, it is the model's or an out-of-gas failure that rolls back.
* An input that is no call fails with no effects.
* No execution reports an interpreter limitation.

Gas and the trie are the only observations not compared exactly.
-/

namespace NearInterface

open Wasm.Near ContractModel

/-- Agreement on everything except gas and the trie. A success agrees on the
return value, storage, balance, storage usage, logs and receipts (encoded with
`prepaid - used` as leftover gas). The balance loses exactly the receipts'
deposits; truncation covers the protocol's one-yocto subsidy, which applies
only at zero balance. A failure agrees on the failure and the logs, and
leaves storage, balance, usage and receipts as they were. -/
def Matches (M : ContractModel) (ctx : Context) (raw : RawStorage) (r : Observation) :
    StepResult M.Panic M.State M.Ret M.Promise → Prop
  | .ok o =>
    let receipts := M.encodeReceipts (ctx.prepaidGas - r.usedGas) o.promises
    r.outcome = .ok (M.encodeRet o.ret) ∧
    r.storage = M.encodeState o.state ∧
    r.balance = ctx.balance + ctx.attached - receiptDeposits receipts ∧
    r.storageUsage = ctx.storageUsage - storageUsageOf ctx.protocol raw +
      storageUsageOf ctx.protocol (M.encodeState o.state) ∧
    r.logs = o.logs ∧
    r.receipts = receipts
  | .error f =>
    r.outcome = .error (ModelFailure.toFailure M f.failure) ∧
    r.storage = raw ∧ r.balance = ctx.balance ∧ r.storageUsage = ctx.storageUsage ∧
    r.logs = f.logs ∧ r.receipts = []

/-- A failed call with no effects. -/
def RolledBack (ctx : Context) (raw : RawStorage) (r : Observation) : Prop :=
  (∃ f, r.outcome = .error f) ∧ r.storage = raw ∧ r.balance = ctx.balance ∧
    r.storageUsage = ctx.storageUsage ∧ r.receipts = []

def Refines (R : RuntimeInterface) (protocol : RuntimeConfig) (code : R.Code) (M : ContractModel) :
    Prop :=
  ∀ raw st ctx, M.Represents raw st → ctx.WF raw → ctx.protocol = protocol →
    let r := R.exec code raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    -- valid calls
    (∀ c, M.Parses ctx.method ctx.args c →
      let res := M.step ctx st c
      (M.gas ctx st c ≤ ctx.gasLimit →
        Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
      (Matches M ctx raw r res ∨
        (r.outcome = .error .outOfGas ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs))) ∧
    -- everything that is not a call fails with no effects
    ((¬ ∃ c, M.Parses ctx.method ctx.args c) → RolledBack ctx raw r)

namespace Refines

variable {R : RuntimeInterface} {protocol : RuntimeConfig} {code : R.Code} {M : ContractModel}
  {raw : RawStorage} {st : Option M.State} {ctx : Context}

/-- With enough gas, a property of the model step is a property of the binary. -/
theorem transfer (h : Refines R protocol code M) (hrep : M.Represents raw st) (hwf : ctx.WF raw)
    (hprot : ctx.protocol = protocol)
    {c : M.Call} (hparse : M.Parses ctx.method ctx.args c) (hgas : M.gas ctx st c ≤ ctx.gasLimit) :
    Matches M ctx raw (R.exec code raw ctx) (M.step ctx st c) :=
  (((h raw st ctx hrep hwf hprot).2.1 c hparse).1 hgas).1

/-- With enough gas, the binary uses no more than the model's bound. -/
theorem gas_bound (h : Refines R protocol code M) (hrep : M.Represents raw st) (hwf : ctx.WF raw)
    (hprot : ctx.protocol = protocol)
    {c : M.Call} (hparse : M.Parses ctx.method ctx.args c) (hgas : M.gas ctx st c ≤ ctx.gasLimit) :
    (R.exec code raw ctx).usedGas ≤ M.gas ctx st c :=
  (((h raw st ctx hrep hwf hprot).2.1 c hparse).1 hgas).2

/-- Input that is no call never changes storage, balance or receipts. -/
theorem invalid_input (h : Refines R protocol code M) (hrep : M.Represents raw st) (hwf : ctx.WF raw)
    (hprot : ctx.protocol = protocol)
    (hinvalid : ¬ ∃ c, M.Parses ctx.method ctx.args c) :
    RolledBack ctx raw (R.exec code raw ctx) :=
  (h raw st ctx hrep hwf hprot).2.2 hinvalid

theorem no_execution_issue (h : Refines R protocol code M) (hrep : M.Represents raw st) (hwf : ctx.WF raw)
    (hprot : ctx.protocol = protocol)
    (msg : String) : (R.exec code raw ctx).outcome ≠ .error (.executionIssue msg) :=
  (h raw st ctx hrep hwf hprot).1 msg

/-- Every failed execution rolls back storage, balance, usage and receipts. -/
theorem failure_rollback (h : Refines R protocol code M) (hrep : M.Represents raw st) (hwf : ctx.WF raw)
    (hprot : ctx.protocol = protocol)
    {f : Failure} (hfail : (R.exec code raw ctx).outcome = .error f) :
    RolledBack ctx raw (R.exec code raw ctx) := by
  by_cases hvalid : ∃ c, M.Parses ctx.method ctx.args c
  · obtain ⟨c, hparse⟩ := hvalid
    rcases ((h raw st ctx hrep hwf hprot).2.1 c hparse).2 with hmatch | ⟨_, hrb, _⟩
    · cases hres : M.step ctx st c with
      | ok o =>
        rw [hres] at hmatch
        have := hmatch.1
        rw [hfail] at this
        cases this
      | error e =>
        rw [hres] at hmatch
        obtain ⟨hout, hs, hb, hu, _, hr⟩ := hmatch
        exact ⟨⟨_, hout⟩, hs, hb, hu, hr⟩
    · exact hrb
  · exact h.invalid_input hrep hwf hprot hvalid

end Refines

end NearInterface
