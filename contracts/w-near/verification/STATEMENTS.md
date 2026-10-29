# Pinned statements

Generated from `statements.json` by the axiom audit with `--update-statements`.
The audit fails when a statement here differs from the build: a change to
this file is a change to what the proofs prove, and is reviewed as one.

## NearInterface.Model

`NearInterface.ContractModel` (hash `349cee7a0e610b6d`)

```lean
inductive NearInterface.ContractModel : Type 1
| NearInterface.ContractModel.mk (State Call Ret Panic Promise : Type) (encodeState : State → NearInterface.RawStorage)
  (Inv : State → Prop) (Parses : String → Wasm.Near.Bytes → Call → Prop) (encodeRet : Ret → Wasm.Near.ReturnData)
  (encodeReceipts : NearInterface.Gas → List Promise → List NearInterface.RawReceipt)
  (panicFailure : Panic → NearInterface.Failure)
  (step : NearInterface.Context → Option State → Call → NearInterface.StepResult Panic State Ret Promise)
  (gas : NearInterface.Context → Option State → Call → NearInterface.Gas)
  (proofBound : NearInterface.Context → Option State → Call → ℕ) : NearInterface.ContractModel
```

`NearInterface.ContractModel.ModelFailure.toFailure` (hash `c6c4a85579466f8f`)

```lean
def NearInterface.ContractModel.ModelFailure.toFailure (M : NearInterface.ContractModel) :
  NearInterface.ModelFailure M.Panic → NearInterface.Failure :=
  fun x =>
    match x with
    | NearInterface.ModelFailure.panic p => M.panicFailure p
    | NearInterface.ModelFailure.balanceExceeded => NearInterface.Failure.balanceExceeded
    | NearInterface.ModelFailure.lackBalanceForState deficit =>
      NearInterface.Failure.lackBalanceForState deficit
    | NearInterface.ModelFailure.logLimit error => NearInterface.Failure.other error.message
    | NearInterface.ModelFailure.receiptInvalid message => NearInterface.Failure.other message
```

`NearInterface.ContractModel.ParsesFunctional` (hash `e204fc1a79346714`)

```lean
def NearInterface.ContractModel.ParsesFunctional (M : NearInterface.ContractModel) : Prop :=
  ∀ (method : String) (args : Wasm.Near.Bytes) (c c' : M.Call),
    M.Parses method args c → M.Parses method args c' → c = c'
```

`NearInterface.ContractModel.Represents` (hash `20341de58f81fa7d`)

```lean
def NearInterface.ContractModel.Represents (M : NearInterface.ContractModel) (raw : NearInterface.RawStorage) :
  Option M.State → Prop :=
  fun x =>
    match x with
    | none => raw = ∅
    | some s => M.Inv s ∧ raw = M.encodeState s
```

`NearInterface.Failed` (hash `b9a17449971bea9c`)

```lean
inductive NearInterface.Failed (Panic : Type) : Type
| NearInterface.Failed.mk {Panic : Type} (failure : NearInterface.ModelFailure Panic) (logs : List String) :
  NearInterface.Failed Panic
```

`NearInterface.ModelFailure` (hash `123ec05bbd86d494`)

```lean
inductive NearInterface.ModelFailure (Panic : Type) : Type
| NearInterface.ModelFailure.panic {Panic : Type} (p : Panic) : NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.balanceExceeded {Panic : Type} : NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.lackBalanceForState {Panic : Type} (deficit : NearInterface.Balance) :
  NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.logLimit {Panic : Type} (error : Wasm.Near.HostError) : NearInterface.ModelFailure Panic
| NearInterface.ModelFailure.receiptInvalid {Panic : Type} (message : String) : NearInterface.ModelFailure Panic
```

`NearInterface.Outcome` (hash `8a0717d03380c7a4`)

```lean
inductive NearInterface.Outcome (State Ret Promise : Type) : Type
| NearInterface.Outcome.mk {State Ret Promise : Type} (state : State) (ret : Ret) (logs : List String)
  (promises : List Promise) : NearInterface.Outcome State Ret Promise
```

`NearInterface.StepResult` (hash `98f034d930bb6e84`)

```lean
def NearInterface.StepResult (Panic State Ret Promise : Type) : Type :=
  Except (NearInterface.Failed Panic) (NearInterface.Outcome State Ret Promise)
```

`NearInterface.StepResult.logs` (hash `775de7047fd2bda4`)

```lean
def NearInterface.StepResult.logs {Panic State Ret Promise : Type} :
  NearInterface.StepResult Panic State Ret Promise → List String :=
  fun x =>
    match x with
    | Except.ok o => o.logs
    | Except.error f => f.logs
```

`NearInterface.logLimitError` (hash `abd90ad08d8f8dab`)

```lean
def NearInterface.logLimitError (cfg : Wasm.Near.RuntimeConfig) (logs : List String) :
  Option (Wasm.Near.HostError × List String) :=
  NearInterface.logLimitError.go cfg 0 [] logs
```

`NearInterface.logLimitError.go` (hash `65eb75879978768e`)

```lean
def NearInterface.logLimitError.go (cfg : Wasm.Near.RuntimeConfig) (total : ℕ) (kept : List String) :
  List String → Option (Wasm.Near.HostError × List String) :=
  fun a =>
    List.brecOn (motive := fun a => ℕ → List String → Option (Wasm.Near.HostError × List String))
      a (NearInterface.logLimitError.go._f cfg) total kept
```

`NearInterface.returnDataGas` (hash `1543dfe90219aad2`)

```lean
def NearInterface.returnDataGas (ctx : NearInterface.Context) (bytes : ℕ) : NearInterface.Gas :=
  have fee := ctx.protocol.fees.actionFees.newDataReceiptByte;
  (List.map (fun r => (fee.send (decide (r = ctx.current)) + fee.execution) * bytes)
      ctx.outputDataReceivers).sum
```

## NearInterface.Refines

`NearInterface.Matches` (hash `37564aad8bda2995`)

```lean
def NearInterface.Matches (M : NearInterface.ContractModel) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
  (r : NearInterface.Observation) : NearInterface.StepResult M.Panic M.State M.Ret M.Promise → Prop :=
  fun x =>
    match x with
    | Except.ok o =>
      have receipts := M.encodeReceipts (ctx.prepaidGas - r.usedGas) o.promises;
      r.outcome = Except.ok (M.encodeRet o.ret) ∧
        r.storage = M.encodeState o.state ∧
          r.balance = ctx.balance + ctx.attached - NearInterface.receiptDeposits receipts ∧
            r.storageUsage =
                ctx.storageUsage - NearInterface.storageUsageOf ctx.protocol raw +
                  NearInterface.storageUsageOf ctx.protocol (M.encodeState o.state) ∧
              r.logs = o.logs ∧ r.receipts = receipts
    | Except.error f =>
      r.outcome = Except.error (NearInterface.ContractModel.ModelFailure.toFailure M f.failure) ∧
        r.storage = raw ∧
          r.balance = ctx.balance ∧
            r.storageUsage = ctx.storageUsage ∧ r.logs = f.logs ∧ r.receipts = []
```

`NearInterface.Refines` (hash `e8d3ec6936af5ac7`)

```lean
def NearInterface.Refines (R : NearInterface.RuntimeInterface) (protocol : Wasm.Near.RuntimeConfig) (code : R.Code)
  (M : NearInterface.ContractModel) : Prop :=
  ∀ (raw : NearInterface.RawStorage) (st : Option M.State) (ctx : NearInterface.Context),
    M.Represents raw st →
      ctx.WF raw →
        ctx.protocol = protocol →
          have r := R.exec code raw ctx;
          (∀ (msg : String),
              r.outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)) ∧
            (∀ (c : M.Call),
                M.Parses ctx.method ctx.args c →
                  have res := M.step ctx st c;
                  (M.gas ctx st c ≤ ctx.gasLimit →
                      ctx.ProofRoom (M.proofBound ctx st c) →
                        NearInterface.Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
                    (NearInterface.Matches M ctx raw r res ∨
                      NearInterface.ResourceFailure r ∧
                        NearInterface.RolledBack ctx raw r ∧ r.logs <+: res.logs)) ∧
              ((¬∃ c, M.Parses ctx.method ctx.args c) → NearInterface.RolledBack ctx raw r)
```

`NearInterface.Refines.failure_rollback` (hash `00000000e8d827ab`)

```lean
theorem NearInterface.Refines.failure_rollback {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) {f : NearInterface.Failure}
  (hfail : (R.exec code raw ctx).outcome = Except.error f) : NearInterface.RolledBack ctx raw (R.exec code raw ctx)
```

`NearInterface.Refines.gas_bound` (hash `000000001e0678ca`)

```lean
theorem NearInterface.Refines.gas_bound {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) {c : M.Call} (hparse : M.Parses ctx.method ctx.args c)
  (hgas : M.gas ctx st c ≤ ctx.gasLimit) (hproof : ctx.ProofRoom (M.proofBound ctx st c)) :
  (R.exec code raw ctx).usedGas ≤ M.gas ctx st c
```

`NearInterface.Refines.invalid_input` (hash `00000000ec18a34f`)

```lean
theorem NearInterface.Refines.invalid_input {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) (hinvalid : ¬∃ c, M.Parses ctx.method ctx.args c) :
  NearInterface.RolledBack ctx raw (R.exec code raw ctx)
```

`NearInterface.Refines.no_execution_issue` (hash `00000000bc1f4254`)

```lean
theorem NearInterface.Refines.no_execution_issue {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State}
  {ctx : NearInterface.Context} (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st)
  (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) (msg : String) :
  (R.exec code raw ctx).outcome ≠ Except.error (NearInterface.Failure.executionIssue msg)
```

`NearInterface.Refines.transfer` (hash `0000000051c57a82`)

```lean
theorem NearInterface.Refines.transfer {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig} {code : R.Code}
  {M : NearInterface.ContractModel} {raw : NearInterface.RawStorage} {st : Option M.State} {ctx : NearInterface.Context}
  (h : NearInterface.Refines R protocol code M) (hrep : M.Represents raw st) (hwf : ctx.WF raw)
  (hprot : ctx.protocol = protocol) {c : M.Call} (hparse : M.Parses ctx.method ctx.args c)
  (hgas : M.gas ctx st c ≤ ctx.gasLimit) (hproof : ctx.ProofRoom (M.proofBound ctx st c)) :
  NearInterface.Matches M ctx raw (R.exec code raw ctx) (M.step ctx st c)
```

`NearInterface.ResourceFailure` (hash `3c862ca5a53f7623`)

```lean
def NearInterface.ResourceFailure (r : NearInterface.Observation) : Prop :=
  r.outcome = Except.error NearInterface.Failure.outOfGas ∨
    r.outcome = Except.error NearInterface.Failure.storageProofExceeded
```

`NearInterface.RolledBack` (hash `f4582bb96b6fbc5a`)

```lean
def NearInterface.RolledBack (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
  (r : NearInterface.Observation) : Prop :=
  (∃ f, r.outcome = Except.error f) ∧
    r.storage = raw ∧
      r.balance = ctx.balance ∧ r.storageUsage = ctx.storageUsage ∧ r.receipts = []
```

## Proofs.Authorization

`WNear.balance_authorization` (hash `00000000890f2136`)

```lean
theorem WNear.balance_authorization : WNear.BalanceAuthorization
```

`WNear.registration_authorization` (hash `00000000e0341f1b`)

```lean
theorem WNear.registration_authorization : WNear.RegistrationAuthorization
```

## Proofs.Availability

`WNear.deposit_available` (hash `00000000cf8a7a6c`)

```lean
theorem WNear.deposit_available : WNear.DepositAvailable
```

`WNear.deposit_available_at_boundary` (hash `000000005177d310`)

```lean
theorem WNear.deposit_available_at_boundary : WNear.DepositAvailableAtBoundary
```

`WNear.withdraw_available` (hash `0000000005c62657`)

```lean
theorem WNear.withdraw_available : WNear.WithdrawAvailable
```

`WNear.withdraw_available_at_boundary` (hash `000000008b8f064c`)

```lean
theorem WNear.withdraw_available_at_boundary : WNear.WithdrawAvailableAtBoundary
```

`WNear.withdraw_available_binary` (hash `00000000e8f4a189`)

```lean
theorem WNear.withdraw_available_binary {R : NearInterface.RuntimeInterface} {protocol : Wasm.Near.RuntimeConfig}
  {code : R.Code} {cfg : WNear.Config} (href : NearInterface.Refines R protocol code (WNear.wnear cfg))
  {s : WNear.State} {ctx : NearInterface.Context} {amount : ℕ} (hs : WNear.Inv cfg s) (hwf : ctx.WF (WNear.encode s))
  (hprot : ctx.protocol = protocol) (hparse : WNear.Parses ctx.method ctx.args (WNear.Call.nearWithdraw amount))
  (hreg : WNear.AccountId.ofNear ctx.predecessor ∈ s.registered)
  (hamt : amount ≤ s.balance (WNear.AccountId.ofNear ctx.predecessor)) (hdep : ctx.attached = 1)
  (hbound : amount + 1 < WNear.u128Bound) (hbal : amount ≤ ctx.balance)
  (hrent :
    NearInterface.stakeDeficit ctx.protocol
        (WNear.usageAfter ctx (some s)
          (have __src :=
            s.setBalance (WNear.AccountId.ofNear ctx.predecessor)
              (s.balance (WNear.AccountId.ofNear ctx.predecessor) - amount);
          { registered := __src.registered, balance := __src.balance, totalSupply := s.totalSupply - amount,
            accountStorageUsage := __src.accountStorageUsage }))
        (ctx.balance - amount) ctx.locked =
      0)
  (hlog :
    NearInterface.logLimitError ctx.protocol
        [toString "Withdraw " ++ toString amount ++ toString " NEAR from " ++
            toString (WNear.AccountId.ofNear ctx.predecessor)] =
      none)
  (hreceipts :
    NearInterface.ReceiptValidation.callReceiptsError ctx.protocol ctx.current ctx.signer ctx.signerPk
        (WNear.encodeReceipts [WNear.Promise.transfer (WNear.AccountId.ofNear ctx.predecessor) (amount + 1)]) =
      none)
  (hgas : WNear.gasBound ctx (WNear.Call.nearWithdraw amount) ≤ ctx.gasLimit)
  (hproof : ctx.ProofRoom (WNear.proofBound ctx)) :
  (R.exec code (WNear.encode s) ctx).outcome = Except.ok (Wasm.Near.ReturnData.receiptIndex 0) ∧
    (R.exec code (WNear.encode s) ctx).storage =
      WNear.encode
        (have __src :=
          s.setBalance (WNear.AccountId.ofNear ctx.predecessor)
            (s.balance (WNear.AccountId.ofNear ctx.predecessor) - amount);
        { registered := __src.registered, balance := __src.balance, totalSupply := s.totalSupply - amount,
          accountStorageUsage := __src.accountStorageUsage })
```

## Proofs.Conservation

`WNear.conservation` (hash `00000000e13d24ac`)

```lean
theorem WNear.conservation : WNear.Conservation
```

## Proofs.Invariants

`WNear.inv_preserved` (hash `000000006db6f3fb`)

```lean
theorem WNear.inv_preserved : WNear.InvPreserved
```

## Proofs.Refinement

`WNear.refines_wnear` (hash `000000001848be87`)

```lean
theorem WNear.refines_wnear (cfg : WNear.Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
  (protocol : Wasm.Near.RuntimeConfig) (hcfg : cfg.WF)
  (hcode : Wasm.Binary.decode WNear.Binary.wNearBytes = Except.ok code)
  (hprotocol : Wasm.Near.RuntimeConfig.parse WNear.wNearProtocolJson = Except.ok protocol) :
  NearInterface.Refines Near.Boundary.nearRuntime protocol
    { code := { module := code, size := WNear.Binary.wNearBytes.size, hash := "" }, codeOf := codeOf } (WNear.wnear cfg)
```

## Proofs.Storage

`WNear.project_encode` (hash `00000000f97dfa6f`)

```lean
theorem WNear.project_encode : WNear.ProjectEncode
```

`WNear.storage_coverage` (hash `00000000fdfdf849`)

```lean
theorem WNear.storage_coverage : WNear.StorageCoverage
```

## Proofs.Views

`WNear.balance_of_correct` (hash `0000000074f20d71`)

```lean
theorem WNear.balance_of_correct : WNear.BalanceOfCorrect
```

`WNear.init_once` (hash `0000000075320071`)

```lean
theorem WNear.init_once : WNear.InitOnce
```

`WNear.total_supply_correct` (hash `0000000029008582`)

```lean
theorem WNear.total_supply_correct : WNear.TotalSupplyCorrect
```

`WNear.views_pure` (hash `0000000008a46ce5`)

```lean
theorem WNear.views_pure : WNear.ViewsPure
```

`WNear.views_total` (hash `00000000d6d9bb0c`)

```lean
theorem WNear.views_total : WNear.ViewsTotal
```

## Spec.Authorization

`WNear.BalanceAuthorization` (hash `b3fe59e56bbdb9cd`)

```lean
def WNear.BalanceAuthorization : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env call = Except.ok o →
        ∀ (a : WNear.AccountId),
          a ≠ env.predecessor →
            o.state.balance a < s.balance a →
              ∃ sender amount,
                call = WNear.Call.ftResolveTransfer sender a amount ∧
                  s.balance a - o.state.balance a ≤ amount
```

`WNear.RegistrationAuthorization` (hash `bfa31c9d6941c45e`)

```lean
def WNear.RegistrationAuthorization : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env call = Except.ok o →
        ∀ a ∈ s.registered, a ∉ o.state.registered → a = env.predecessor
```

## Spec.Availability

`WNear.DepositAvailable` (hash `275c18a892b057eb`)

```lean
def WNear.DepositAvailable : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env),
    WNear.Inv cfg s →
      0 < env.attachedDeposit →
        s.totalSupply + env.attachedDeposit < WNear.u128Bound →
          env.predecessor ∈ s.registered ∨ s.storageMin ≤ env.attachedDeposit →
            ∃ o,
              WNear.step cfg (some s) env WNear.Call.nearDeposit = Except.ok o ∧
                env.predecessor ∈ o.state.registered ∧
                  (o.state.balance env.predecessor +
                        if env.predecessor ∈ s.registered then 0 else s.storageMin) =
                      s.balance env.predecessor + env.attachedDeposit ∧
                    o.promises = []
```

`WNear.DepositAvailableAtBoundary` (hash `65529199857b7a14`)

```lean
def WNear.DepositAvailableAtBoundary : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (ctx : NearInterface.Context),
    have env := WNear.Env.ofContext ctx;
    WNear.Inv cfg s →
      0 < ctx.attached →
        s.totalSupply + ctx.attached < WNear.u128Bound →
          env.predecessor ∈ s.registered ∨ s.storageMin ≤ ctx.attached →
            ∃ o,
              WNear.step (WNear.Config.ofRuntime ctx.protocol) (some s) env
                    WNear.Call.nearDeposit =
                  Except.ok o ∧
                env.predecessor ∈ o.state.registered ∧
                  (o.state.balance env.predecessor +
                        if env.predecessor ∈ s.registered then 0 else s.storageMin) =
                      s.balance env.predecessor + ctx.attached ∧
                    o.promises = [] ∧
                      have deficit :=
                        NearInterface.stakeDeficit ctx.protocol
                          (WNear.usageAfter ctx (some s) o.state) (ctx.balance + ctx.attached)
                          ctx.locked;
                      NearInterface.logLimitError ctx.protocol o.logs = none →
                        WNear.contractStep ctx (some s) WNear.Call.nearDeposit =
                          if 0 < deficit then
                            Except.error
                              { failure := NearInterface.ModelFailure.lackBalanceForState deficit,
                                logs := o.logs }
                          else
                            Except.ok
                              { state := o.state, ret := o.ret, logs := o.logs, promises := [] }
```

`WNear.WithdrawAvailable` (hash `434fc06075b1c6be`)

```lean
def WNear.WithdrawAvailable : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (amount : ℕ),
    WNear.Inv cfg s →
      env.predecessor ∈ s.registered →
        amount ≤ s.balance env.predecessor →
          env.attachedDeposit = 1 →
            amount + 1 < WNear.u128Bound →
              WNear.step cfg (some s) env (WNear.Call.nearWithdraw amount) =
                Except.ok
                  {
                    state :=
                      have __src :=
                        s.setBalance env.predecessor (s.balance env.predecessor - amount);
                      { registered := __src.registered, balance := __src.balance,
                        totalSupply := s.totalSupply - amount,
                        accountStorageUsage := __src.accountStorageUsage },
                    promises := [WNear.Promise.transfer env.predecessor (amount + 1)],
                    ret := WNear.Ret.promise 0,
                    logs :=
                      [toString "Withdraw " ++ toString amount ++ toString " NEAR from " ++
                          toString env.predecessor] }
```

`WNear.WithdrawAvailableAtBoundary` (hash `ce6d8bc4ad971d17`)

```lean
def WNear.WithdrawAvailableAtBoundary : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (ctx : NearInterface.Context) (amount : ℕ),
    have a := WNear.AccountId.ofNear ctx.predecessor;
    have s' :=
      have __src := s.setBalance a (s.balance a - amount);
      { registered := __src.registered, balance := __src.balance,
        totalSupply := s.totalSupply - amount, accountStorageUsage := __src.accountStorageUsage };
    WNear.Inv cfg s →
      a ∈ s.registered →
        amount ≤ s.balance a →
          ctx.attached = 1 →
            amount + 1 < WNear.u128Bound →
              amount ≤ ctx.balance →
                NearInterface.stakeDeficit ctx.protocol (WNear.usageAfter ctx (some s) s')
                      (ctx.balance - amount) ctx.locked =
                    0 →
                  NearInterface.logLimitError ctx.protocol
                        [toString "Withdraw " ++ toString amount ++ toString " NEAR from " ++
                            toString a] =
                      none →
                    NearInterface.ReceiptValidation.callReceiptsError ctx.protocol ctx.current
                          ctx.signer ctx.signerPk
                          (WNear.encodeReceipts [WNear.Promise.transfer a (amount + 1)]) =
                        none →
                      WNear.contractStep ctx (some s) (WNear.Call.nearWithdraw amount) =
                        Except.ok
                          { state := s', ret := WNear.Ret.promise 0,
                            logs :=
                              [toString "Withdraw " ++ toString amount ++
                                    toString " NEAR from " ++
                                  toString a],
                            promises := [WNear.Promise.transfer a (amount + 1)] }
```

## Spec.Conservation

`WNear.Conservation` (hash `b91c36f2bfeb20d5`)

```lean
def WNear.Conservation : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env call = Except.ok o →
        ↑o.state.totalSupply - ↑s.totalSupply +
            ↑s.storageMin * (↑o.state.registered.card - ↑s.registered.card) ≤
          ↑env.attachedDeposit - ↑o.nearOut
```

## Spec.Contract

`WNear.wnear` (hash `997da11be2c01ee4`)

```lean
def WNear.wnear (cfg : WNear.Config) : NearInterface.ContractModel :=
  { State := WNear.State, Call := WNear.Call, Ret := WNear.Ret, Panic := WNear.Panic,
    Promise := WNear.Promise, encodeState := WNear.encode, Inv := WNear.Inv cfg,
    Parses := WNear.Parses, encodeRet := WNear.encodeRet,
    encodeReceipts := fun x => WNear.encodeReceipts, panicFailure := WNear.Panic.failure,
    step := WNear.contractStep, gas := fun ctx x c => WNear.gasBound ctx c,
    proofBound := fun ctx x x_1 => WNear.proofBound ctx }
```

`WNear.wnear_parsesFunctional` (hash `00000000fee36cb6`)

```lean
theorem WNear.wnear_parsesFunctional (cfg : WNear.Config) : (WNear.wnear cfg).ParsesFunctional
```

## Spec.Exports

`WNear.exportedMethods` (hash `bd3fd7cbc3b6baf6`)

```lean
def WNear.exportedMethods : List String :=
  ["storage_minimum_balance", "near_deposit", "near_withdraw", "new", "ft_transfer",
    "ft_transfer_call", "ft_total_supply", "ft_balance_of", "ft_resolve_transfer",
    "storage_deposit", "storage_withdraw", "storage_unregister", "storage_balance_bounds",
    "storage_balance_of", "ft_metadata"]
```

`WNear.funcExportNames` (hash `18dcbdb5f054dc17`)

```lean
def WNear.funcExportNames (m : Wasm.Module) : List String :=
  List.filterMap
    (fun e =>
      match e.desc with
      | Wasm.ExportDesc.func i => some e.name
      | x => none)
    m.exports.toList
```

## Spec.Invariants

`WNear.Config.WF` (hash `cdf8f2c7b4098ab6`)

```lean
def WNear.Config.WF (cfg : WNear.Config) : Prop :=
  cfg.measuredAccountStorageUsage < WNear.u64Bound
```

`WNear.Inv` (hash `9c58883e2b30905f`)

```lean
inductive WNear.Inv (cfg : WNear.Config) (s : WNear.State) : Prop
| WNear.Inv.mk {cfg : WNear.Config} {s : WNear.State} (toWF : s.WF) (supply : s.supply = s.totalSupply)
  (usage : s.accountStorageUsage = cfg.measuredAccountStorageUsage) : WNear.Inv cfg s
```

`WNear.InvPreserved` (hash `9055243458cf8585`)

```lean
def WNear.InvPreserved : Prop :=
  ∀ (cfg : WNear.Config) (st : Option WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    cfg.WF →
      (∀ (s : WNear.State), st = some s → WNear.Inv cfg s) →
        WNear.step cfg st env call = Except.ok o → WNear.Inv cfg o.state
```

## Spec.Storage

`WNear.ProjectEncode` (hash `f83de85fe675beb6`)

```lean
def WNear.ProjectEncode : Prop :=
  ∀ (s : WNear.State), s.WF → WNear.project (WNear.encode s) = some s
```

`WNear.StorageCoverage` (hash `a4c035b02fb893e8`)

```lean
def WNear.StorageCoverage : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State),
    WNear.Inv cfg s →
      WNear.storageUsage cfg (WNear.encode s) ≤
        cfg.recordBytes (WNear.stateKey, WNear.header s) +
          s.registered.card * s.accountStorageUsage
```

## Spec.Views

`WNear.BalanceOfCorrect` (hash `fb181a48e89a6bec`)

```lean
def WNear.BalanceOfCorrect : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (a : WNear.AccountId)
    (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env (WNear.Call.ftBalanceOf a) = Except.ok o →
        o.ret = WNear.Ret.u128 (s.balance a)
```

`WNear.InitOnce` (hash `380260cbce064460`)

```lean
def WNear.InitOnce : Prop :=
  (∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env),
      env.attachedDeposit = 0 →
        WNear.step cfg (some s) env WNear.Call.new =
          Except.error WNear.Panic.alreadyInitialized) ∧
    ∀ (cfg : WNear.Config) (env : WNear.Env) (call : WNear.Call),
      call ≠ WNear.Call.new → ∃ p, WNear.step cfg none env call = Except.error p
```

`WNear.TotalSupplyCorrect` (hash `5460da1e157c6d7c`)

```lean
def WNear.TotalSupplyCorrect : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (o : WNear.Outcome),
    WNear.Inv cfg s →
      WNear.step cfg (some s) env WNear.Call.ftTotalSupply = Except.ok o →
        o.ret = WNear.Ret.u128 s.supply
```

`WNear.ViewsPure` (hash `c14c5058c68f8efd`)

```lean
def WNear.ViewsPure : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call)
    (o : WNear.Outcome),
    call.isView = true →
      WNear.step cfg (some s) env call = Except.ok o → o.state = s ∧ o.promises = [] ∧ o.logs = []
```

`WNear.ViewsTotal` (hash `c5873a3d24413009`)

```lean
def WNear.ViewsTotal : Prop :=
  ∀ (cfg : WNear.Config) (s : WNear.State) (env : WNear.Env) (call : WNear.Call),
    call.isView = true → ∃ o, WNear.step cfg (some s) env call = Except.ok o
```
