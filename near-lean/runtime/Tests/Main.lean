import NearRuntime
import Tests.Decoder
import Tests.Gas
import Tests.Shard
import Wasm.Wat

/-!
# Runtime scenario tests

`lake exe runtime-tests [wat-path] [configs-dir]`. Deploys the real wNEAR
binary on `wrap.near` and drives it with transactions through `apply`,
settling all receipts between steps. Checks balances, receipts, refunds,
failure handling and the conservation of NEAR.
-/

open Wasm Wasm.Near Near

def oneNear : Nat := 10 ^ 24
def tgas (n : Nat) : Nat := n * 10 ^ 12
def registrationFee : Nat := 125 * 10 ^ 19

def pkOf (seed : UInt8) : PublicKey := 0 :: List.replicate 32 seed

/-- Standard compressed Edwards25519 basepoint, suitable for staking. -/
def stakingPk : PublicKey := 0 :: 0x58 :: List.replicate 31 0x66
def bytesOf (s : String) : List UInt8 := s.toUTF8.toList
def strOf (b : List UInt8) : String := (String.fromUTF8? ⟨b.toArray⟩).getD "<bad utf8>"

structure Report where
  failed : Nat := 0
  passed : Nat := 0

def check (r : IO.Ref Report) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    r.modify fun s => { s with passed := s.passed + 1 }
    IO.println s!"ok: {name}"
  else
    r.modify fun s => { s with failed := s.failed + 1 }
    IO.println s!"FAIL: {name}{if detail.isEmpty then "" else s!" — {detail}"}"

/-- The chain under test: state, receipts in flight, nonces, burnt tokens. -/
structure World where
  cfg : RuntimeConfig
  code : ContractCode
  state : ChainState
  pending : List Receipt := []
  nonces : List (AccountId × Nat) := []
  burnt : Nat := 0
  /-- All outcomes so far, newest last. -/
  outcomes : List (ReceiptId × ExecutionOutcome) := []
  issue : Option (ReceiptId × ExecutionIssue) := none

def World.ap : ApplyState := { gasPrice := 100_000_000, gasLimit := none }

def World.account (w : World) (id : AccountId) : Account :=
  (w.state.account? id).getD { amount := 0, storageUsage := 0 }

/-- One apply. -/
def World.apply1 (w : World) (txs : List Transaction) : World :=
  let r := Near.apply w.cfg World.ap (fun _ => w.code) w.state txs w.pending
  if r.issue.isSome then { w with issue := r.issue }
  else { w with state := r.state, pending := r.outgoing, burnt := w.burnt + r.tokensBurnt,
                outcomes := w.outcomes ++ r.outcomes }

/-- Apply until no receipt is in flight. -/
def World.settle (w : World) (txs : List Transaction) (fuel : Nat := 32) : World :=
  let rec go : Nat → World → World
    | 0, w => w
    | n + 1, w => if w.issue.isSome || (w.pending.isEmpty && w.state.delayed.isEmpty) then w else go n (w.apply1 [])
  go fuel (w.apply1 txs)

def World.tx (w : World) (signer receiver : AccountId) (actions : List Action) : Transaction × World :=
  let n := (Assoc.lookup w.nonces signer).getD 0 + 1
  let pk := pkOf (if signer == "alice.near" then 1 else if signer == "bob.near" then 2 else 3)
  ({ signerId := signer, publicKey := pk, nonce := n, receiverId := receiver, actions },
   { w with nonces := Assoc.insert w.nonces signer n })

def World.call (w : World) (signer : AccountId) (method : String) (args : String) (deposit : Nat)
    (gas : Nat := tgas 100) : World :=
  let (tx, w) := w.tx signer "wrap.near" [.functionCall method (bytesOf args) gas deposit]
  w.settle [tx]

/-- A view call straight into the VM on the current storage. -/
def World.view (w : World) (method : String) (args : String) : Option String :=
  let ctx : VMContext :=
    { currentAccountId := bytesOf "wrap.near", signerAccountId := bytesOf "bob.near", signerAccountPk := []
      predecessorAccountId := bytesOf "bob.near", input := bytesOf args, prepaidGas := tgas 300
      viewConfig := some { maxGasBurnt := tgas 300 } }
  let o := run w.cfg w.code.module w.code.size method ctx (w.state.contractStorage "wrap.near")
  match o.returnData with
  | .value b => some (strOf b)
  | _ => none

/-- NEAR conservation: what was minted at genesis is still accounted for. -/
def World.total (w : World) : Nat :=
  w.state.totalBalance + w.burnt +
    ((w.pending ++ w.state.delayed ++ w.state.postponed.map (·.2)).map (Fees.receiptFunds w.cfg)).sum

def genesisAccount (amount : Nat) : Account := { amount, storageUsage := 182 }

def latestOutcome (w : World) (p : ExecutionOutcome → Bool) : Option ExecutionOutcome :=
  (w.outcomes.reverse.find? fun (_, o) => p o).map (·.2)

def isFailure (o : Option ExecutionOutcome) (p : RuntimeError → Bool) : Bool :=
  match o with
  | some { status := .failure e, .. } => p e
  | _ => false

/-- Transaction acceptance and receipt execution occupy different chunks
unless the signer is also the receiver. These checks observe each frontier. -/
def checkTransactionRouting (r : IO.Ref Report) (cfg : RuntimeConfig) (code : ContractCode)
    (genesis : ChainState) : IO Unit := do
  let tx : Transaction := {
    signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "bob.near"
    actions := [.transfer oneNear] }
  let sent := Near.apply cfg World.ap (fun _ => code) genesis [tx] []
  check r "cross-account transaction emits an outgoing action receipt"
    (sent.issue.isNone && sent.outgoing.length == 1 && sent.state.delayed.isEmpty
      && sent.outgoing.all fun receipt =>
        receipt.predecessorId == "alice.near" && receipt.receiverId == "bob.near"
          && Fees.totalDeposit receipt.actions == oneNear)
  check r "cross-account acceptance has only a transaction outcome"
    (sent.outcomes.length == 1 && sent.outcomes.all fun (_, outcome) =>
      outcome.executorId == "alice.near" && match outcome.status with
        | .successReceiptId id => sent.outgoing.any (·.receiptId == id)
        | _ => false)
  check r "cross-account acceptance charges the signer without crediting the receiver"
    ((sent.state.account? "alice.near").map (fun account => decide (account.amount < 100 * oneNear)) == some true
      && (sent.state.account? "bob.near").map (·.amount) == some (10 * oneNear)
      && (sent.state.accessKey? "alice.near" (pkOf 1)).map (·.nonce) == some 1)
  let delivered := Near.apply cfg World.ap (fun _ => code) sent.state [] sent.outgoing
  check r "the receiver is credited only when the transaction receipt is delivered"
    (delivered.issue.isNone && (delivered.state.account? "bob.near").map (·.amount) == some (11 * oneNear)
      && delivered.outcomes.any fun (_, outcome) => outcome.executorId == "bob.near" && outcome.status.isSuccess)
  let localResult := Near.apply cfg World.ap (fun _ => code) genesis [{ tx with receiverId := "alice.near" }] []
  check r "signer-is-receiver actions execute in the transaction chunk"
    (localResult.issue.isNone && localResult.outcomes.length == 2
      && localResult.outcomes.all (fun (_, outcome) => outcome.status.isSuccess)
      && localResult.outgoing.all Receipt.isRefund)
  let limited := Near.apply cfg { World.ap with gasLimit := some 0 } (fun _ => code) genesis [tx] []
  check r "outgoing transaction receipts do not enter the local gas-delay queue"
    (limited.state.delayed.isEmpty && limited.outgoing.length == 1
      && (limited.state.account? "bob.near").map (·.amount) == some (10 * oneNear))
  let limitedLocal := Near.apply cfg { World.ap with gasLimit := some 0 } (fun _ => code)
    genesis [{ tx with receiverId := "alice.near" }] []
  check r "zero chunk budget defers local receipts before any execution"
    (limitedLocal.outcomes.length == 1 && limitedLocal.state.delayed.length == 1 &&
      limitedLocal.outgoing.isEmpty && limitedLocal.outcomes.all fun (_, o) =>
        match o.status with | .successReceiptId _ => true | _ => false)
  let incoming : Receipt := {
    predecessorId := "carol.near", receiverId := "bob.near", receiptId := 100
    receipt := .action {
      signerId := "carol.near", signerPublicKey := pkOf 4
      gasPrice := 0, actions := [.transfer 7] } }
  let mixed := Near.apply cfg World.ap (fun _ => code) genesis
    [tx, { tx with receiverId := "alice.near", nonce := 2 }] [incoming]
  check r "mixed blocks execute local receipts before incoming receipts"
    (mixed.issue.isNone && mixed.outcomes.map (·.2.executorId) ==
      ["alice.near", "alice.near", "alice.near", "bob.near"]
      && (mixed.state.account? "bob.near").map (·.amount) == some (10 * oneNear + 7)
      && (mixed.outgoing.head?.map (·.receiverId)) == some "bob.near")

/-- Restricted-key availability across real VM execution and delayed refunds. -/
def checkRefundScenarios (r : IO.Ref Report) (cfg : RuntimeConfig) (code : ContractCode)
    (base : ChainState) : IO Unit := do
  let accountId := "alice.near"
  let pk := pkOf 42
  let args := bytesOf "{\"account_id\":\"alice.near\"}"
  let actions := [Action.functionCall "ft_balance_of" args (tgas 50) 0]
  let cost := Fees.txCost cfg World.ap.gasPrice accountId "wrap.near" actions
  let reserve := cost.total / 2
  let install (state : ChainState) (pk : PublicKey) (key : AccessKey) : ChainState :=
    let account := (state.account? accountId).getD (genesisAccount 0)
    let oldBytes := ((state.accessKey? accountId pk).map fun old =>
      accessKeyStorageBytes pk old + cfg.fees.numExtraBytesRecord).getD 0
    let bytes := accessKeyStorageBytes pk key + cfg.fees.numExtraBytesRecord
    (state.setAccount accountId { account with storageUsage := account.storageUsage + bytes - oldBytes }).setAccessKey accountId pk key
  let allowanceOf (state : ChainState) (pk : PublicKey) : Option Nat :=
    (state.accessKey? accountId pk).bind fun key => match key.permission with
      | .functionCall allowance _ _ => allowance | _ => none
  let initial := install base pk {
    nonce := 0
    permission := .functionCall (some (cost.total + reserve)) "wrap.near" ["ft_balance_of"] }
  let tx (nonce : Nat) : Transaction := {
    signerId := accountId, publicKey := pk, nonce, receiverId := "wrap.near", actions }
  let submitted := Near.apply cfg World.ap (fun _ => code) initial [tx 1] []
  let first := Near.apply cfg World.ap (fun _ => code) submitted.state [] submitted.outgoing
  let refunds := first.outgoing.filter Receipt.isGasRefund
  let amount := (refunds.map fun receipt => Fees.totalDeposit receipt.actions).sum
  check r "gas refund: restricted call consumes its purchased allowance and emits the key marker"
    (first.issue.isNone && first.outgoing.length == 1 && refunds.length == 1 && amount > 0 &&
      allowanceOf first.state pk == some reserve && refunds.all fun receipt => match receipt.receipt with
        | .action action => action.signerId == accountId && action.signerPublicKey == pk
        | _ => false)
  let beforeRefund := Near.apply cfg World.ap (fun _ => code) first.state [tx 2] []
  check r "gas refund: another call is rejected before its allowance returns"
    (beforeRefund.tokensBurnt == 0 && beforeRefund.outcomes.any fun (_, outcome) => match outcome.status with
      | .failure (.notEnoughAllowance ..) => true | _ => false)
  let restored := Near.apply cfg World.ap (fun _ => code) first.state [] first.outgoing
  check r "gas refund: restores allowance exactly without double-crediting account funds"
    (restored.issue.isNone && restored.tokensBurnt == 0 && restored.outgoing.isEmpty &&
      allowanceOf restored.state pk == some (reserve + amount) &&
      restored.state.totalBalance == first.state.totalBalance + amount)
  let submittedAgain := Near.apply cfg World.ap (fun _ => code) restored.state [tx 2] []
  let second := Near.apply cfg World.ap (fun _ => code) submittedAgain.state [] submittedAgain.outgoing
  check r "gas refund: restored allowance permits the next restricted call"
    (second.issue.isNone && second.outcomes.any fun (_, outcome) =>
      outcome.executorId == "wrap.near" && outcome.status.isSuccess)
  let old := (first.state.accessKey? accountId pk).getD { nonce := 0, permission := .fullAccess }
  let oldAccount := (first.state.account? accountId).getD (genesisAccount 0)
  let removed := (first.state.setAccount accountId { oldAccount with
    storageUsage := oldAccount.storageUsage - accessKeyStorageBytes pk old - cfg.fees.numExtraBytesRecord }).removeAccessKey accountId pk
  let deleted := Near.apply cfg World.ap (fun _ => code) removed [] first.outgoing
  check r "gas refund: deleted key stays deleted while its account receives the refund"
    ((deleted.state.accessKey? accountId pk).isNone && deleted.state.totalBalance == removed.totalBalance + amount)
  for (name, replacement, expected) in
      [("finite", ({ nonce := 17, permission := .functionCall (some 5) "other.near" ["other"] } : AccessKey),
         ({ nonce := 17, permission := .functionCall (some (5 + amount)) "other.near" ["other"] } : AccessKey)),
       ("unlimited", { nonce := 18, permission := .functionCall none "other.near" ["other"] },
         { nonce := 18, permission := .functionCall none "other.near" ["other"] }),
       ("full access", { nonce := 19, permission := .fullAccess }, { nonce := 19, permission := .fullAccess })] do
    let state := install first.state pk replacement
    let result := Near.apply cfg World.ap (fun _ => code) state [] first.outgoing
    check r s!"gas refund: follows the current {name} replacement key"
      (result.issue.isNone && result.state.accessKey? accountId pk == some expected &&
        result.state.totalBalance == state.totalBalance + amount)
  let emptyKey : AccessKey := { nonce := 2, permission := .functionCall (some 7) "wrap.near" [] }
  let balanceState := install first.state emptyPublicKey emptyKey
  let balance := (refundReceipt balanceState accountId 23).1
  let balanceResult := Near.apply cfg World.ap (fun _ => code) balanceState [] [balance]
  check r "balance refund: matching empty public key does not restore its allowance"
    (!balance.isGasRefund && balanceResult.state.accessKey? accountId emptyPublicKey == some emptyKey &&
      balanceResult.state.totalBalance == balanceState.totalBalance + 23)
  let ordinary : Receipt := {
    predecessorId := "wrap.near", receiverId := accountId, receiptId := 999
    receipt := .action { signerId := accountId, signerPublicKey := pk, gasPrice := 0, actions := [.transfer 3] } }
  let ordinaryResult := Near.apply cfg World.ap (fun _ => code) first.state [] [ordinary]
  check r "ordinary transfer: signer metadata never restores an allowance"
    (ordinaryResult.state.accessKey? accountId pk == first.state.accessKey? accountId pk)
  let underfunded := first.state.setAccount accountId { amount := 0, storageUsage := 1_000_000_000 }
  let rolledBack := Near.apply cfg World.ap (fun _ => code) underfunded [] first.outgoing
  check r "failed gas refund: storage-staking rollback discards the allowance update"
    (rolledBack.issue.isNone && rolledBack.tokensBurnt == amount &&
      rolledBack.state.accessKey? accountId pk == underfunded.accessKey? accountId pk &&
      (rolledBack.state.account? accountId).map (·.amount) == some 0)

def main (args : List String) : IO UInt32 := do
  let wat := args[0]?.getD "../vm/tests/fixtures/w_near.wat"
  let configs := args[1]?.getD "../vm/configs"
  let r ← IO.mkRef ({} : Report)
  let cfg ← RuntimeConfig.load configs RuntimeConfig.latestVersion
  let decoderChecks ← NearRuntime.Tests.Decoder.run cfg
  let gasChecks ← NearRuntime.Tests.Gas.run cfg
  let shardChecks ← NearRuntime.Tests.Shard.run
  r.modify fun report => { report with passed := report.passed + decoderChecks + gasChecks + shardChecks }
  let text ← IO.FS.readFile wat
  let module ← match ← Wat.compile text with
    | .ok m => pure m
    | .error e => do IO.println s!"decode error: {e}"; return 1
  let code : ContractCode := { module, size := 200_000, hash := "w_near" }
  let fullAccess : AccessKey := { nonce := 0, permission := .fullAccess }
  let genesis : ChainState :=
    { accounts := [("alice.near", genesisAccount (100 * oneNear)), ("bob.near", genesisAccount (10 * oneNear)),
                   ("wrap.near", genesisAccount (10 * oneNear))]
      accessKeys := [(("alice.near", pkOf 1), fullAccess), (("bob.near", pkOf 2), fullAccess),
                     (("wrap.near", pkOf 3), fullAccess)] }
  let w0 : World := { cfg, code, state := genesis }
  let total0 := w0.total
  check r "genesis total is 120 NEAR" (total0 = 120 * oneNear)
  checkTransactionRouting r cfg code genesis

  let seedState := genesis.setAccount "wrap.near" { genesisAccount (10 * oneNear) with code := some code }
  let seedTx : Transaction := {
    signerId := "wrap.near", publicKey := pkOf 3, nonce := 1, receiverId := "wrap.near"
    actions := [.functionCall "ft_metadata" [] (tgas 50) 0] }
  let parentHash : Near.Bytes := List.replicate 32 7
  for (label, ap, expected) in [
      ("missing parent", { World.ap with nativeReceiptHashes := some [] }, "native identity is unavailable"),
      ("malformed parent", { World.ap with nativeReceiptHashes := some [(1, [7])] }, "invalid identity hash width"),
      ("duplicate parent", { World.ap with nativeReceiptHashes := some [(1, parentHash), (1, parentHash)] }, "duplicate model identity"),
      ("malformed block seed", { World.ap with nativeReceiptHashes := some [(1, parentHash)], randomSeed := [7] }, "invalid identity hash width")] do
    let attempted := Near.apply cfg ap (fun _ => code) seedState [seedTx] []
    check r s!"native randomness {label} is an explicit context issue"
      ((attempted.issue.map (·.2)) == some (.interpreterError s!"Native action randomness context: {expected}"))
    check r s!"native randomness {label} rolls back the entire chunk"
      (attempted.outgoing.isEmpty && attempted.outcomes.isEmpty && attempted.tokensBurnt == 0 &&
        attempted.identityBirths.isEmpty && attempted.delayedConsumed == 0 && attempted.delayedAppended == 0 &&
        attempted.state.totalBalance == seedState.totalBalance && attempted.state.nextId == seedState.nextId &&
        attempted.state.accessKeys == seedState.accessKeys)

  for (name, action) in
      [("deploy", Action.deployContract code),
       ("add key", Action.addKey (pkOf 4) fullAccess),
       ("delete key", Action.deleteKey (pkOf 3)),
       ("delete account", Action.deleteAccount "alice.near"),
       ("stake", Action.stake oneNear stakingPk)] do
    let tx : Transaction := {
      signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "wrap.near"
      actions := [.transfer oneNear, action] }
    let submitted := Near.apply cfg World.ap (fun _ => code) genesis [tx] []
    let attempt := Near.apply cfg World.ap (fun _ => code) submitted.state [] submitted.outgoing
    check r s!"foreign actor cannot {name} on wrap.near"
      (attempt.outcomes.any fun (_, o) => match o.status with
        | .failure (.actorNoPermission "wrap.near" "alice.near") => true
        | _ => false)
    check r s!"denied {name} rolls back the preceding transfer"
      ((attempt.state.account? "wrap.near").map (·.amount) == some (10 * oneNear))
    check r s!"denied {name} is a protocol failure, not a model issue" attempt.issue.isNone

  let created := "child.alice.near"
  let createTx : Transaction := {
    signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := created
    actions := [.createAccount, .transfer (3 * oneNear), .addKey (pkOf 4) fullAccess, .deployContract code] }
  let createSubmitted := Near.apply cfg World.ap (fun _ => code) genesis [createTx] []
  let createResult := Near.apply cfg World.ap (fun _ => code) createSubmitted.state [] createSubmitted.outgoing
  check r "account creation grants authority for subsequent key and code actions"
    (createResult.issue.isNone && createResult.outcomes.all (fun (_, o) => o.status.isSuccess) &&
      createResult.state.accessKey? created (pkOf 4) == some fullAccess &&
      ((createResult.state.account? created).bind (·.code)).isSome)

  -- Native AccountId::is_top_level excludes the reserved system actor.
  let relaxedCreation := { cfg with accountCreation := { cfg.accountCreation with minAllowedTopLevelAccountLength := 0 } }
  check r "reserved system creation is denied to the registrar"
    (!canCreateAccount cfg cfg.accountCreation.registrarAccountId systemAccount)
  check r "reserved system creation ignores a zero top-level length limit"
    (!canCreateAccount relaxedCreation "alice.near" systemAccount)
  check r "reserved system rule permits an ordinary lookalike name"
    (canCreateAccount relaxedCreation "alice.near" "systemx")
  check r "reserved system rule permits an ordinary subaccount prefix"
    (canCreateAccount cfg cfg.accountCreation.registrarAccountId ("system." ++ cfg.accountCreation.registrarAccountId))
  let registrarGenesis := (genesis.setAccount cfg.accountCreation.registrarAccountId (genesisAccount (10 * oneNear))).setAccessKey
    cfg.accountCreation.registrarAccountId (pkOf 9) fullAccess
  for (label, creationCfg, signer, key) in
      [("registrar", cfg, cfg.accountCreation.registrarAccountId, pkOf 9),
       ("zero length limit", relaxedCreation, "alice.near", pkOf 1)] do
    let tx : Transaction := {
      signerId := signer, publicKey := key, nonce := 1, receiverId := systemAccount
      actions := [.createAccount, .transfer (3 * oneNear), .addKey (pkOf 8) fullAccess, .deployContract code] }
    let initial : World := { cfg := creationCfg, code, state := registrarGenesis }
    let denied := initial.settle [tx]
    check r s!"reserved system {label}: creation is a protocol rejection"
      (denied.issue.isNone && denied.outcomes.any (fun (_, outcome) => match outcome.status with
        | .failure (.createAccountNotAllowed receiver predecessor) => receiver == systemAccount && predecessor == signer
        | _ => false))
    check r s!"reserved system {label}: no account or authority is installed"
      ((denied.state.account? systemAccount).isNone && (denied.state.accessKey? systemAccount (pkOf 8)).isNone)
    check r s!"reserved system {label}: rejection conserves funds including refunds and fees"
      (denied.pending.isEmpty && denied.total == initial.total)

  let multiTransfer : Transaction := {
    signerId := "alice.near", publicKey := pkOf 1, nonce := 1
    receiverId := String.ofList (List.replicate 64 'a')
    actions := [.transfer oneNear, .addKey (pkOf 4) fullAccess] }
  let implicitSubmitted := Near.apply cfg World.ap (fun _ => code) genesis [multiTransfer] []
  let invalidImplicit := Near.apply cfg World.ap (fun _ => code) implicitSubmitted.state [] implicitSubmitted.outgoing
  check r "implicit creation cannot be followed by an attacker-controlled key"
    ((invalidImplicit.state.account? multiTransfer.receiverId).isNone &&
      invalidImplicit.outcomes.any fun (_, o) => !o.status.isSuccess)

  -- An unsupported operation invalidates the model attempt, not the contract.
  -- Neither charged transactions, queued outgoing receipts nor a preceding
  -- successfully executed local receipt in the same apply may be committed.
  let unsupportedModule ← match ← Wat.compile
      "(module (import \"env\" \"sha256\" (func $hash (param i64 i64 i64)))
       (memory 1) (func (export \"test\") i64.const 0 i64.const 0 i64.const 0 call $hash))" with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"unsupported runtime fixture: {e}")
  let unsupportedCode : ContractCode := { module := unsupportedModule, size := 0, hash := "unsupported-fixture" }
  let unsupportedState := genesis.setAccount "wrap.near"
    { genesisAccount (10 * oneNear) with code := some unsupportedCode }
  let transferTx : Transaction := {
    signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "bob.near"
    actions := [.transfer oneNear] }
  let unsupportedTx : Transaction := {
    signerId := "wrap.near", publicKey := pkOf 3, nonce := 1, receiverId := "wrap.near"
    actions := [.functionCall "test" [] (tgas 50) oneNear] }
  let localTransferTx : Transaction := {
    signerId := "bob.near", publicKey := pkOf 2, nonce := 1, receiverId := "bob.near"
    actions := [.transfer oneNear] }
  let stopped := Near.apply cfg World.ap (fun _ => unsupportedCode) unsupportedState
    [transferTx, localTransferTx, unsupportedTx] []
  check r "unsupported host is an apply issue, not a receipt failure"
    ((stopped.issue.map (·.2)) == some (.unsupportedHost "sha256"))
  check r "unsupported apply publishes no outcomes, refunds or burnt tokens"
    (stopped.outcomes.isEmpty && stopped.outgoing.isEmpty && stopped.tokensBurnt == 0)
  check r "unsupported apply rolls back prior transfers and charged transaction balances"
    (stopped.state.totalBalance == unsupportedState.totalBalance &&
     (stopped.state.account? "bob.near").map (·.amount) == some (10 * oneNear) &&
     (stopped.state.account? "alice.near").map (·.amount) == some (100 * oneNear))
  check r "unsupported apply rolls back nonces and receipt identifiers"
    (stopped.state.accessKey? "alice.near" (pkOf 1) == some fullAccess &&
     stopped.state.nextId == unsupportedState.nextId)
  let crossUnsupported := { unsupportedTx with signerId := "alice.near", publicKey := pkOf 1, nonce := 2 }
  let accepted := Near.apply cfg World.ap (fun _ => unsupportedCode) unsupportedState
    [transferTx, crossUnsupported] []
  let rejectedDelivery := Near.apply cfg World.ap (fun _ => unsupportedCode) accepted.state [] accepted.outgoing
  check r "unsupported contract execution is discovered at delivery, not transaction acceptance"
    (accepted.issue.isNone && accepted.outgoing.length == 2 && accepted.outcomes.length == 2
      && rejectedDelivery.issue.map (·.2) == some (.unsupportedHost "sha256"))
  check r "a delivery issue retains already committed transaction charges and nonces"
    (rejectedDelivery.state.totalBalance == accepted.state.totalBalance
      && rejectedDelivery.state.accessKey? "alice.near" (pkOf 1) == accepted.state.accessKey? "alice.near" (pkOf 1)
      && rejectedDelivery.state.nextId == accepted.state.nextId
      && rejectedDelivery.state.totalBalance < unsupportedState.totalBalance)

  let stakedState := genesis.setAccount "wrap.near"
    { genesisAccount (10 * oneNear) with locked := oneNear }
  let unstakeTx : Transaction := {
    signerId := "wrap.near", publicKey := pkOf 3, nonce := 1, receiverId := "wrap.near"
    actions := [.stake 0 stakingPk] }
  let unstake := Near.apply cfg World.ap (fun _ => code) stakedState [unstakeTx] []
  check r "unstaking explicitly requires unmodelled epoch semantics"
    ((unstake.issue.map (·.2)) == some (.unsupportedAction "unstake (epoch machinery)"))
  check r "unsupported unstaking leaves locked funds untouched"
    ((unstake.state.account? "wrap.near").map (·.locked) == some oneNear)

  -- Fee classification and explicit unsupported implicit-creation semantics.
  let cfg69 ← RuntimeConfig.load configs 69
  let cfg70 ← RuntimeConfig.load configs 70
  check r "ETH implicit account flag follows the protocol configuration"
    (!cfg69.wasm.ethImplicitAccounts && cfg70.wasm.ethImplicitAccounts && cfg.wasm.ethImplicitAccounts)
  for (label, receiver) in [("ETH", "0x" ++ String.ofList (List.replicate 40 'a')),
      ("deterministic", "0s" ++ String.ofList (List.replicate 40 'a'))] do
    let tx : Transaction := {
      signerId := "alice.near", publicKey := pkOf 1, nonce := 1
      receiverId := receiver, actions := [.transfer oneNear] }
    let submitted := Near.apply cfg World.ap (fun _ => code) genesis [tx] []
    check r s!"{label} implicit transfer submits an outgoing receipt before receiver execution"
      (submitted.issue.isNone && submitted.outgoing.length == 1 &&
        (submitted.state.accessKey? "alice.near" (pkOf 1)).map (·.nonce) == some 1)
    let missing := Near.apply cfg World.ap (fun _ => code) submitted.state [] submitted.outgoing
    check r s!"{label} implicit creation installs the account on delivery"
      (missing.issue.isNone && (missing.state.account? receiver).map (·.amount) == some oneNear)
    check r s!"{label} implicit account has the wallet identity (ETH) or none (deterministic)"
      (match (missing.state.account? receiver) with
        | some a => a.global.isSome == (label == "ETH") && a.code.isNone
        | none => false)
    if label == "ETH" then
      let legacy := { cfg with wasm := { cfg.wasm with ethImplicitGlobalContract := false } }
      let legacyMissing := Near.apply legacy World.ap (fun _ => code) submitted.state [] submitted.outgoing
      check r "legacy ETH wallet creation reports a model issue and rolls back delivery"
        ((legacyMissing.issue.map (·.2)) ==
            some (.unsupportedAction "ETH-implicit account creation with the legacy wallet contract") &&
          (legacyMissing.state.account? receiver).isNone && legacyMissing.state.nextId == submitted.state.nextId &&
          legacyMissing.outcomes.isEmpty && legacyMissing.outgoing.isEmpty && legacyMissing.tokensBurnt == 0)
    let present := genesis.setAccount receiver (genesisAccount oneNear)
    let sent := Near.apply cfg World.ap (fun _ => code) present [tx] []
    let applied := Near.apply cfg World.ap (fun _ => code) sent.state [] sent.outgoing
    check r s!"{label} existing receiver accepts a transfer"
      (sent.issue.isNone && applied.issue.isNone &&
        (applied.state.account? receiver).map (·.amount) == some (2 * oneNear))
    let total := applied.state.totalBalance + (applied.outgoing.map (Fees.receiptFunds cfg)).sum +
      sent.tokensBurnt + applied.tokensBurnt
    check r s!"{label} existing receiver transfer conserves funds and gas backing" (total == present.totalBalance)
    check r s!"{label} explicit create is rejected as implicit creation"
      (match checkActionAccount genesis { predecessorId := "alice.near", receiverId := receiver, receiptId := 0, receipt := .data { dataId := 0, data := none } } true .createAccount true with
        | .error (.onlyImplicitAccountCreationAllowed id) => id == receiver
        | _ => false)
  let disabledReceipt : Receipt := {
    predecessorId := "alice.near", receiverId := "0x" ++ String.ofList (List.replicate 40 'a')
    receiptId := 0, receipt := .data { dataId := 0, data := none } }
  check r "disabled ETH implicit receiver is treated as a missing named account"
    (match checkActionAccount genesis disabledReceipt true (.transfer 1) false with
      | .error (.accountDoesNotExist _) => true | _ => false)

  let implicitTarget := String.ofList (List.replicate 64 'a')
  let implicitWat := "(module (import \"env\" \"promise_batch_create\" (func $batch (param i64 i64) (result i64))) " ++
    "(import \"env\" \"promise_batch_action_transfer\" (func $transfer (param i64 i64))) (memory 1) " ++
    "(data (i32.const 0) \"" ++ implicitTarget ++ "\") (data (i32.const 80) \"\\01\") " ++
    "(func (export \"send\") i64.const 64 i64.const 0 call $batch i64.const 80 call $transfer))"
  let implicitModule ← match ← Wat.compile implicitWat with
    | .ok m => pure m
    | .error error => throw (IO.userError s!"implicit transfer fixture: {error}")
  let implicitCode : ContractCode := { module := implicitModule, size := 0, hash := "implicit-transfer-fixture" }
  let implicitState := genesis.setAccount "wrap.near" { genesisAccount (10 * oneNear) with code := some implicitCode }
  let implicitWorld : World := { cfg, code := implicitCode, state := implicitState }
  let implicitResult := implicitWorld.call "alice.near" "send" "{}" 0
  check r "VM-created implicit transfer settles and creates the NEAR receiver"
    (implicitResult.issue.isNone && implicitResult.pending.isEmpty && implicitResult.state.delayed.isEmpty &&
      implicitResult.state.postponed.isEmpty && (implicitResult.state.account? implicitTarget).map (·.amount) == some 1)
  check r "VM-created implicit transfer conserves deposits, fees and refunds"
    (implicitResult.total == implicitWorld.total && implicitResult.burnt > 0)

  -- Raw deployment length must not be supplied by the external module decoder.
  let deployWat := "(module (import \"env\" \"promise_batch_create\" (func $batch (param i64 i64) (result i64))) " ++
    "(import \"env\" \"promise_batch_action_deploy_contract\" (func $deploy (param i64 i64 i64))) (memory 1) " ++
    "(data (i32.const 0) \"wrap.near\") (data (i32.const 16) \"\\00asm\\01\\00\\00\\00\") " ++
    "(func (export \"deploy\") i64.const 9 i64.const 0 call $batch i64.const 8 i64.const 16 call $deploy))"
  let deployModule ← match ← Wat.compile deployWat with
    | .ok module => pure module
    | .error error => throw (IO.userError s!"deployment fixture: {error}")
  let emptyModule ← match ← Wat.compile "(module)" with
    | .ok module => pure module
    | .error error => throw (IO.userError s!"empty deployment fixture: {error}")
  let decodedCode : ContractCode := {
    module := emptyModule, size := cfg.wasm.limits.maxContractSize + 1, hash := "empty-wasm" }
  let deployingCode : ContractCode := { module := deployModule, size := 0, hash := "deploying-fixture" }
  let deploymentState := genesis.setAccount "wrap.near" { genesisAccount (10 * oneNear) with code := some deployingCode }
  let deployApply := Near.apply cfg World.ap (fun _ => decodedCode)
  let deployCall : Transaction := {
    signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "wrap.near"
    actions := [.functionCall "deploy" [] (tgas 50) 0] }
  let admittedDeploy := deployApply deploymentState [deployCall] []
  let scheduledDeploy := deployApply admittedDeploy.state [] admittedDeploy.outgoing
  check r "promise deployment uses raw byte length in outgoing gas backing"
    (scheduledDeploy.issue.isNone && scheduledDeploy.state.totalBalance + admittedDeploy.tokensBurnt +
      scheduledDeploy.tokensBurnt + (scheduledDeploy.outgoing.map (Fees.receiptFunds cfg)).sum == deploymentState.totalBalance)
  let executedDeploy := deployApply scheduledDeploy.state [] scheduledDeploy.outgoing
  check r "promise deployment stores actual byte size and storage usage despite decoder metadata"
    (executedDeploy.issue.isNone && executedDeploy.outcomes.all (fun (_, o) => o.status.isSuccess) &&
      ((executedDeploy.state.account? "wrap.near").bind (·.code)).map (·.size) == some 8 &&
      (executedDeploy.state.account? "wrap.near").map (·.storageUsage) == some 190)
  let refundedDeploy := deployApply executedDeploy.state [] executedDeploy.outgoing
  check r "promise deployment conserves funds through execution and refunds"
    (refundedDeploy.issue.isNone && refundedDeploy.outgoing.isEmpty &&
      refundedDeploy.state.totalBalance + admittedDeploy.tokensBurnt + scheduledDeploy.tokensBurnt +
        executedDeploy.tokensBurnt + refundedDeploy.tokensBurnt == deploymentState.totalBalance)

  -- Runtime externals reject method bytes before materializing typed actions.
  let methodWat ← IO.FS.readFile "../../tools/runtime-conformance/fixtures/method_encoding.wat"
  let methodBytes ← IO.FS.readBinFile "../../tools/runtime-conformance/fixtures/method_encoding.wasm"
  let methodModule ← match ← Wat.compile methodWat with
    | .ok module => pure module
    | .error error => throw (IO.userError s!"method encoding fixture: {error}")
  let methodCode : ContractCode := { module := methodModule, size := methodBytes.size, hash := "method-encoding-fixture" }
  let methodState := genesis.setAccount "wrap.near" {
    genesisAccount (10 * oneNear) with code := some methodCode, storageUsage := 182 + methodCode.size }
  let methodWorld : World := { cfg, code := methodCode, state := methodState }
  for method in ["batch_bad", "create_bad", "then_bad", "key_bad"] do
    let failed := methodWorld.call "alice.near" method "{}" 0
    let outcome := latestOutcome failed fun o => o.executorId == "wrap.near"
    check r s!"runtime {method}: invalid UTF-8 rejects with native error and preserves earlier logs"
      (failed.issue.isNone && isFailure outcome (· == .functionCallError (.hostError .invalidMethodName)) &&
        outcome.map (·.logs) == some ["before"])
    check r s!"runtime {method}: rejection conserves funds and creates no access key"
      (failed.total == methodWorld.total && failed.pending.isEmpty && failed.state.postponed.isEmpty &&
        (failed.state.accessKey? "wrap.near" (pkOf 0)).isNone)
  let validMethod := methodWorld.call "alice.near" "batch_valid" "{}" 0
  check r "runtime method encoding: valid Unicode passes external validation"
    (validMethod.outcomes.any (fun (_, o) => o.executorId == "wrap.near" && o.status.isSuccess &&
      o.logs == ["before", "after"]) && validMethod.issue.isNone)
  let validKey := methodWorld.call "alice.near" "key_valid" "{}" 0
  check r "runtime method encoding: Unicode key permissions retain exact names"
    ((validKey.state.accessKey? "wrap.near" (pkOf 0)).map (·.permission) ==
      some (.functionCall none "alice.near" ["λ", "ok"]))
  check r "runtime method encoding: successful key scheduling conserves gas backing"
    (validKey.issue.isNone && validKey.total == methodWorld.total && validKey.pending.isEmpty)

  -- deploy and initialise in one transaction from wrap.near
  let (txDeploy, w) := w0.tx "wrap.near" "wrap.near" [.deployContract code, .functionCall "new" (bytesOf "{}") (tgas 50) 0]
  let w := w.settle [txDeploy]
  check r "deploy + new: contract installed" ((w.account "wrap.near").code.isSome)
  check r "deploy + new: STATE written" ((w.state.contractStorage "wrap.near").any fun kv => kv.1 == bytesOf "STATE")
  check r "deploy + new: storage usage counts the code and the record"
    ((w.account "wrap.near").storageUsage = 182 + 200_000 + 74) s!"{(w.account "wrap.near").storageUsage}"
  check r "deploy + new: no receipt in flight" (w.pending.isEmpty && w.state.delayed.isEmpty)
  check r "deploy + new: NEAR conserved" (w.total = total0) s!"{w.total} vs {total0}"
  check r "deploy + new: gas was paid" (w.burnt > 0 && (w.account "wrap.near").amount < 10 * oneNear)
  check r "deploy + new: outcome is a success"
    ((latestOutcome w fun o => o.executorId == "wrap.near" && o.logs.isEmpty).map (·.status.isSuccess) == some true)

  -- alice wraps 1 NEAR
  let aliceBefore := (w.account "alice.near").amount
  let wrapBefore := (w.account "wrap.near").amount
  let w := w.call "alice.near" "near_deposit" "{}" oneNear
  check r "near_deposit: wNEAR minted" (w.view "ft_balance_of" "{\"account_id\":\"alice.near\"}"
    == some s!"\"{oneNear - registrationFee}\"")
  check r "near_deposit: logged" ((latestOutcome w fun o => !o.logs.isEmpty).map (·.logs)
    == some [s!"Deposit {oneNear - registrationFee} NEAR to alice.near"])
  check r "near_deposit: wrap.near holds the NEAR plus its gas reward"
    ((w.account "wrap.near").amount > wrapBefore + oneNear) s!"{(w.account "wrap.near").amount - wrapBefore}"
  check r "near_deposit: alice paid 1 NEAR plus a little gas"
    (aliceBefore - oneNear - (w.account "alice.near").amount < oneNear / 100 &&
     (w.account "alice.near").amount < aliceBefore - oneNear)
  check r "near_deposit: unused gas was refunded (a refund receipt ran)"
    (w.outcomes.any fun (_, o) => o.executorId == "alice.near" && o.status.isSuccess && o.tokensBurnt == 0)
  check r "near_deposit: NEAR conserved" (w.total = total0) s!"{w.total} vs {total0}"

  -- alice unwraps 0.3 NEAR
  let amount := 3 * 10 ^ 23
  let aliceBefore := (w.account "alice.near").amount
  let w := w.call "alice.near" "near_withdraw" s!"\{\"amount\":\"{amount}\"}" 1
  check r "near_withdraw: balance drops" (w.view "ft_balance_of" "{\"account_id\":\"alice.near\"}"
    == some s!"\"{oneNear - registrationFee - amount}\"")
  check r "near_withdraw: alice received the NEAR back (minus gas)"
    ((w.account "alice.near").amount > aliceBefore + amount - oneNear / 100 &&
     (w.account "alice.near").amount < aliceBefore + amount)
  check r "near_withdraw: the transfer receipt ran as a success"
    (w.outcomes.any fun (_, o) => o.executorId == "alice.near" && o.status.isSuccess)
  check r "near_withdraw: NEAR conserved" (w.total = total0) s!"{w.total} vs {total0}"

  -- a transfer-call to an account without a contract: callback refunds everything
  let w := w.call "bob.near" "storage_deposit" "{}" registrationFee
  let before := w.view "ft_balance_of" "{\"account_id\":\"alice.near\"}"
  let w := w.call "alice.near" "ft_transfer_call" "{\"receiver_id\":\"bob.near\",\"amount\":\"1000\",\"msg\":\"hi\"}" 1
  check r "ft_transfer_call: ft_on_transfer on an account without code fails"
    (isFailure (latestOutcome w fun o => o.executorId == "bob.near" && !o.status.isSuccess)
      fun e => e == .functionCallError (.compilationError "CodeDoesNotExist"))
  check r "ft_transfer_call: the callback ran and refunded"
    ((latestOutcome w fun o => o.logs.any (·.startsWith "Refund")).map (·.status) == some (.successValue (bytesOf "\"0\"")))
  check r "ft_transfer_call: alice's wNEAR is back" (w.view "ft_balance_of" "{\"account_id\":\"alice.near\"}" == before)
  check r "ft_transfer_call: bob's wNEAR is 0" (w.view "ft_balance_of" "{\"account_id\":\"bob.near\"}" == some "\"0\"")
  check r "ft_transfer_call: nothing postponed remains" (w.state.postponed.isEmpty && w.state.receivedData.isEmpty)
  check r "ft_transfer_call: NEAR conserved" (w.total = total0) s!"{w.total} vs {total0}"

  -- not enough gas: the receipt fails, the deposit comes back
  let aliceBefore := (w.account "alice.near").amount
  let receiverBefore := (w.account "wrap.near").amount
  let w := w.call "alice.near" "near_deposit" "{}" oneNear (gas := 10 ^ 11)
  check r "out of gas: receipt fails with GasExceeded"
    (isFailure (latestOutcome w fun o => o.executorId == "wrap.near")
      fun e => e == .functionCallError (.hostError .gasExceeded))
  check r "out of gas: the deposit was refunded"
    (aliceBefore - (w.account "alice.near").amount < oneNear / 100) s!"{aliceBefore - (w.account "alice.near").amount}"
  check r "out of gas: NEAR conserved" (w.total = total0)
  check r "out of gas: surviving receiver earns burnt function-call gas reward"
    ((w.account "wrap.near").amount > receiverBefore)

  -- invalid transactions
  let badNonce : Transaction :=
    { signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "wrap.near", actions := [.transfer 1] }
  let w := w.settle [badNonce]
  check r "stale nonce is rejected" (isFailure (latestOutcome w fun _ => true) fun e => match e with
    | .invalidNonce _ _ => true | _ => false)
  let (tooRich, w) := w.tx "bob.near" "alice.near" [.transfer (1000 * oneNear)]
  let w := w.settle [tooRich]
  check r "overspending is rejected" (isFailure (latestOutcome w fun _ => true) fun e => match e with
    | .notEnoughBalance .. => true | _ => false)
  let (noKey, w) := w.tx "nobody.near" "alice.near" [.transfer 1]
  let w := w.settle [noKey]
  check r "unknown signer is rejected" (isFailure (latestOutcome w fun _ => true) fun e => match e with
    | .invalidSigner _ => true | _ => false)
  check r "rejected transactions change nothing" (w.total = total0)

  -- implicit account, then delete bob to alice
  let implicit := "".pushn 'a' 64
  let (txI, w) := w.tx "bob.near" implicit [.transfer oneNear]
  let w := w.settle [txI]
  check r "transfer creates the implicit account" ((w.account implicit).amount = oneNear)
  let implicitPk : PublicKey := 0 :: List.replicate 32 170
  check r "implicit account gets the decoded Ed25519 full-access key"
    ((w.state.accessKey? implicit implicitPk).isSome)
  check r "ASCII hex is not installed as an implicit public key"
    ((w.state.accessKey? implicit (0 :: bytesOf implicit)).isNone)
  let implicitTx : Transaction := {
    signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := implicit
    actions := [.transfer oneNear] }
  let implicitSent := Near.apply cfg { World.ap with blockHeight := 7 } (fun _ => code) genesis [implicitTx] []
  check r "implicit accounts do not exist before their transfer receipt arrives"
    ((implicitSent.state.account? implicit).isNone)
  let implicitAtHeight := Near.apply cfg { World.ap with blockHeight := 9 } (fun _ => code)
    implicitSent.state [] implicitSent.outgoing
  check r "implicit key nonce begins in the creation block's nonce range"
    ((implicitAtHeight.state.accessKey? implicit implicitPk).map (·.nonce) == some 8_000_000)
  let aliceBefore := (w.account "alice.near").amount
  let bobAmount := (w.account "bob.near").amount
  let (txD, w) := w.tx "bob.near" "bob.near" [.deleteAccount "alice.near"]
  let w := w.settle [txD]
  check r "delete_account removes bob" ((w.state.account? "bob.near").isNone)
  check r "delete_account pays the beneficiary" ((w.account "alice.near").amount > aliceBefore &&
    (w.account "alice.near").amount ≤ aliceBefore + bobAmount) s!"{(w.account "alice.near").amount - aliceBefore}"
  check r "end: NEAR conserved" (w.total = total0) s!"{w.total} vs {total0}"

  -- gas limit: receipts beyond the limit are delayed, then run
  let (tx1, w') := w.tx "alice.near" "wrap.near" [.functionCall "near_deposit" (bytesOf "{}") (tgas 50) oneNear]
  let (tx2, w') := w'.tx "alice.near" "wrap.near" [.functionCall "near_deposit" (bytesOf "{}") (tgas 50) oneNear]
  let submitted := Near.apply w'.cfg World.ap (fun _ => w'.code) w'.state [tx1, tx2] w'.pending
  let r1 := Near.apply w'.cfg { World.ap with gasLimit := some 1 } (fun _ => w'.code)
    submitted.state [] submitted.outgoing
  check r "gas limit: second receipt is delayed" (r1.state.delayed.length = 1) s!"{r1.state.delayed.length}"
  let r2 := Near.apply w'.cfg World.ap (fun _ => w'.code) r1.state [] r1.outgoing
  check r "gas limit: delayed receipt runs in the next apply"
    (r2.state.delayed.isEmpty && r2.outcomes.any fun (_, o) => o.executorId == "wrap.near" && o.status.isSuccess)

  check r "supported scenarios never encounter a model issue" (w.issue.isNone && r1.issue.isNone && r2.issue.isNone)

  let spendToZero : Transaction :=
    { signerId := "alice.near", publicKey := pkOf 1, nonce := 1,
      receiverId := "bob.near", actions := [.transfer 0] }
  let zeroCost := Fees.txCost cfg World.ap.gasPrice "alice.near" "bob.near" spendToZero.actions
  for (usage, accepted) in [(770, true), (771, false)] do
    let zeroSigner := genesis.setAccount "alice.near" { amount := zeroCost.total, storageUsage := usage }
    let result := convertTransaction cfg World.ap zeroSigner spendToZero
    check r s!"storage exemption: signer at {usage} bytes"
      (match result with
       | .ok (state, _, _) => accepted && (state.account? "alice.near").map (·.amount) == some 0
       | .error (.lackBalanceForState _ _) => !accepted
       | _ => false)
  check r "storage staking deficit includes locked balance"
    (storageStakeDeficit cfg { amount := 2, locked := 3, storageUsage := 771 } ==
      771 * cfg.storageAmountPerByte - 5)

  -- Sponsorship is a committed mint only after the whole receipt succeeds.
  let sponsorModule ← match ← Wat.compile "(module\n (import \"env\" \"promise_batch_create\" (func $batch (param i64 i64) (result i64)))\n (import \"env\" \"promise_batch_action_function_call\" (func $call (param i64 i64 i64 i64 i64 i64 i64)))\n (import \"env\" \"promise_batch_action_transfer\" (func $transfer (param i64 i64)))\n (import \"env\" \"panic\" (func $panic))\n (memory 1)\n (data (i32.const 0) \"alice.near\")\n (data (i32.const 16) \"go\")\n (data (i32.const 64) \"\\01\")\n (data (i32.const 80) \"\\02\")\n (func (export \"one\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call)\n (func (export \"twice\") (local i64) i64.const 10 i64.const 0 call $batch local.set 0 local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call)\n (func (export \"zero\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 96 i64.const 0 call $call)\n (func (export \"two\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 80 i64.const 0 call $call)\n (func (export \"transfer\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 64 call $transfer)\n (func (export \"empty\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 0 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call)\n (func (export \"panic\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call call $panic)\n (func (export \"late_failure\") (local i64) i64.const 10 i64.const 0 call $batch local.set 0 local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 80 i64.const 0 call $call)\n)\n" with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"sponsorship fixture: {e}")
  let sponsorCode : ContractCode := { module := sponsorModule, size := 0, hash := "sponsor" }
  let sponsorState (usage : Nat) := genesis.setAccount "wrap.near"
    { amount := 0, storageUsage := usage, code := some sponsorCode }
  let sponsorTx (actions : List Action) : Transaction :=
    { signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "wrap.near", actions }
  let sponsorCall (method : String) : Action := .functionCall method [] (tgas 100) 0
  let fundedTotal := (sponsorState 770).totalBalance
  let sponsorSubmitted := Near.apply cfg World.ap (fun _ => sponsorCode) (sponsorState 770)
    [sponsorTx [sponsorCall "twice"]] []
  let sponsored := Near.apply cfg World.ap (fun _ => sponsorCode)
    sponsorSubmitted.state [] sponsorSubmitted.outgoing
  check r "sponsorship: two grants commit at storage exemption boundary"
    (sponsored.issue.isNone && sponsored.subsidizedAmount == 2 &&
     sponsored.outcomes.any fun (_, o) => o.executorId == "wrap.near" && o.status.isSuccess)
  let outgoingFunds := (sponsored.outgoing.map (Fees.receiptFunds cfg)).sum
  check r "sponsorship: minted funds enter conservation accounting"
    (sponsored.state.totalBalance + outgoingFunds + sponsored.tokensBurnt + sponsorSubmitted.tokensBurnt == fundedTotal + sponsored.subsidizedAmount)
  for (name, actions, usage) in
      [("VM panic", [sponsorCall "panic"], 770),
       ("later action failure", [sponsorCall "one", .deleteKey (pkOf 99)], 770),
       ("later VM failure", [sponsorCall "one", sponsorCall "panic"], 770),
       ("storage staking failure", [sponsorCall "one"], 771)] do
    let submitted := Near.apply cfg World.ap (fun _ => sponsorCode) (sponsorState usage)
      [sponsorTx actions] []
    let result := Near.apply cfg World.ap (fun _ => sponsorCode) submitted.state [] submitted.outgoing
    check r s!"sponsorship: {name} rolls back committed mint and promises"
      (result.issue.isNone && result.subsidizedAmount == 0 &&
       !(result.outgoing.any fun receipt => !receipt.isRefund && Fees.totalDeposit receipt.actions > 0) &&
       result.outcomes.any fun (_, o) => o.executorId == "wrap.near" && !o.status.isSuccess)

  let twoSponsorState := (sponsorState 770).setAccount "bob.near"
    { amount := 0, storageUsage := 770, code := some sponsorCode }
  let secondSponsor := { sponsorTx [sponsorCall "one"] with nonce := 2, receiverId := "bob.near" }
  let twoSubmitted := Near.apply cfg World.ap (fun _ => sponsorCode) twoSponsorState
    [sponsorTx [sponsorCall "one"], secondSponsor] []
  let twoSponsored := Near.apply cfg World.ap (fun _ => sponsorCode) twoSubmitted.state [] twoSubmitted.outgoing
  check r "sponsorship: apply accumulates grants from separate receipts"
    (twoSponsored.issue.isNone && twoSponsored.subsidizedAmount == 2)
  let issueState := (sponsorState 770).setAccount "bob.near"
    { amount := 0, storageUsage := 770, code := some unsupportedCode }
  let issueTx := { secondSponsor with actions := [sponsorCall "test"] }
  let issueSubmitted := Near.apply cfg World.ap (fun _ => sponsorCode) issueState
    [sponsorTx [sponsorCall "one"], issueTx] []
  let issueAfterGrant := Near.apply cfg World.ap (fun _ => sponsorCode) issueSubmitted.state [] issueSubmitted.outgoing
  check r "sponsorship: later model issue discards all earlier grants"
    (issueAfterGrant.issue.isSome && issueAfterGrant.subsidizedAmount == 0 &&
     issueAfterGrant.outgoing.isEmpty && issueAfterGrant.outcomes.isEmpty &&
     issueAfterGrant.tokensBurnt == 0 && issueAfterGrant.state.nextId == issueSubmitted.state.nextId)

  -- Preserve purchased gas while the chain price changes between blocks.
  let (priceTx, priceWorld) := w.tx "alice.near" "wrap.near"
    [.functionCall "near_withdraw" (bytesOf "{\"amount\":\"1\"}") (tgas 100) 1]
  let priceStart := priceWorld.total
  let priceSubmitted := Near.apply cfg World.ap (fun _ => code) priceWorld.state [priceTx] []
  let firstPrice := Near.apply cfg World.ap (fun _ => code) priceSubmitted.state [] priceSubmitted.outgoing
  let firstTokensBurnt := priceSubmitted.tokensBurnt + firstPrice.tokensBurnt
  let funds (result : ApplyResult) := result.state.totalBalance +
    ((result.outgoing ++ result.state.delayed ++ result.state.postponed.map (·.2)).map (Fees.receiptFunds cfg)).sum
  check r "gas purchase: pending promises and refunds preserve all purchased funds"
    (firstPrice.issue.isNone && firstPrice.outgoing.any (fun receipt => !receipt.isRefund) &&
      firstPrice.outcomes.any (fun (_, outcome) => outcome.executorId == "wrap.near" && outcome.status.isSuccess) &&
      funds firstPrice + priceWorld.burnt + firstTokensBurnt == priceStart)
  for nextPrice in [50_000_000, 3_000_000_000] do
    let secondPrice := Near.apply cfg { World.ap with gasPrice := nextPrice } (fun _ => code)
      firstPrice.state [] firstPrice.outgoing
    check r s!"gas purchase: conservation across block price {nextPrice}"
      (secondPrice.issue.isNone && funds secondPrice + priceWorld.burnt + firstTokensBurnt +
        secondPrice.tokensBurnt == priceStart)
  let lostRefund : Receipt := {
    predecessorId := systemAccount, receiverId := "deleted.near", receiptId := 999
    receipt := .action {
      signerId := systemAccount, signerPublicKey := [], gasPrice := 0
      actions := [.transfer 123] } }
  let lost := Near.apply cfg World.ap (fun _ => code) genesis [] [lostRefund]
  check r "failed system refund burns its funds and reports execution gas without gas tokens"
    (lost.issue.isNone && lost.tokensBurnt == 123 && lost.outgoing.isEmpty &&
      lost.outcomes.all fun (_, outcome) => outcome.gasBurnt > 0 && outcome.tokensBurnt == 0)

  let nonceTx (nonce : Nat) (mode : NonceMode) : Transaction := {
    version := if mode == .strict then 1 else 0,
    signerId := "alice.near", publicKey := pkOf 1, nonce, nonceMode := mode,
    receiverId := "bob.near", actions := [.transfer 1] }
  check r "nonce: default apply context starts at height one" (World.ap.blockHeight == 1)
  for (label, nonce, mode, height, expected) in
      [("monotonic jump", 999_999, NonceMode.monotonic, 1, none),
       ("ceiling equality", 1_000_000, NonceMode.monotonic, 1, some (.nonceTooLarge 1_000_000 1_000_000)),
       ("zero height", 1, NonceMode.monotonic, 0, some (.nonceTooLarge 1 0)),
       ("strict increment", 1, NonceMode.strict, 1, none),
       ("strict jump", 2, NonceMode.strict, 1, some (.invalidNonce 2 0)),
       ("stale precedes ceiling", 0, NonceMode.monotonic, 0, some (.invalidNonce 0 0))] do
    let result := convertTransaction cfg { World.ap with blockHeight := height } genesis (nonceTx nonce mode)
    check r s!"nonce: {label}" (match result, expected with
      | .ok _, none => true
      | .error error, some wanted => error == wanted
      | _, _ => false)
  let cfg84 ← RuntimeConfig.load configs 84
  let monoV1 := { nonceTx 1 .monotonic with version := 1 }
  check r "version: monotonic V1 still requires the envelope feature"
    (match convertTransaction cfg84 World.ap genesis monoV1 with
      | .error .invalidTransactionVersion => true | _ => false)
  check r "version: V0 cannot request strict nonces"
    (match convertTransaction cfg World.ap genesis { nonceTx 1 .strict with version := 0 } with
      | .error .invalidTransactionVersion => true | _ => false)
  check r "version: envelope gate is independent of the strict nonce flag"
    (match convertTransaction { cfg with v1TransactionsEnabled := false } World.ap genesis monoV1 with
      | .error .invalidTransactionVersion => true | _ => false)
  check r "version: monotonic V1 does not require strict nonce activation"
    (match convertTransaction { cfg with strictNonceEnabled := false } World.ap genesis monoV1 with
      | .ok _ => true | _ => false)
  check r "version: unknown envelope tag cannot commit"
    (match convertTransaction cfg World.ap genesis { monoV1 with version := 2 } with
      | .error .invalidTransactionVersion => true | _ => false)
  let earlyStrict := { nonceTx 1 .strict with signerId := "nobody.near" }
  check r "nonce: strict version gate precedes account admission"
    (match convertTransaction cfg84 World.ap genesis earlyStrict with
     | .error .invalidTransactionVersion => true | _ => false)
  let rejectedNonce := Near.apply cfg World.ap (fun _ => code) genesis [nonceTx 1_000_000 .monotonic] []
  check r "nonce: rejected ceiling leaves balance, key, counter and fees untouched"
    (rejectedNonce.tokensBurnt == 0 && rejectedNonce.outgoing.isEmpty &&
      rejectedNonce.state.nextId == genesis.nextId &&
      (rejectedNonce.state.account? "alice.near").map (·.amount) == (genesis.account? "alice.near").map (·.amount) &&
      (rejectedNonce.state.accessKey? "alice.near" (pkOf 1)).map (·.nonce) == some 0)
  let sequencedNonce := Near.apply cfg World.ap (fun _ => code) genesis
    [nonceTx 1 .strict, nonceTx 3 .strict, nonceTx 2 .strict] []
  check r "nonce: strict admission uses prior accepted transactions and ignores rejection"
    ((sequencedNonce.state.accessKey? "alice.near" (pkOf 1)).map (·.nonce) == some 2 &&
      (sequencedNonce.outcomes.take 3).map (fun (_, outcome) => outcome.status.isSuccess) == [true, false, true])

  checkRefundScenarios r cfg code w.state

  let s ← r.get
  IO.println s!"{s.passed} passed, {s.failed} failed"
  return (if s.failed = 0 then 0 else 1)
