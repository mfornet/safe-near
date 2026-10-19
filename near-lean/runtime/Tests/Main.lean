import NearRuntime
import Interpreter.Wasm.Decoder.Wat

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
  w.state.totalBalance + w.burnt + (w.pending.map fun r => Fees.totalDeposit r.actions).sum

def genesisAccount (amount : Nat) : Account := { amount, storageUsage := 182 }

def latestOutcome (w : World) (p : ExecutionOutcome → Bool) : Option ExecutionOutcome :=
  (w.outcomes.reverse.find? fun (_, o) => p o).map (·.2)

def isFailure (o : Option ExecutionOutcome) (p : RuntimeError → Bool) : Bool :=
  match o with
  | some { status := .failure e, .. } => p e
  | _ => false

def main (args : List String) : IO UInt32 := do
  let wat := args[0]?.getD "../vm/tests/fixtures/w_near.wat"
  let configs := args[1]?.getD "../vm/configs"
  let r ← IO.mkRef ({} : Report)
  let cfg ← RuntimeConfig.load configs RuntimeConfig.latestVersion
  let text ← IO.FS.readFile wat
  let module ← match Decoder.Wat.decode text with
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

  for (name, action) in
      [("deploy", Action.deployContract code),
       ("add key", Action.addKey (pkOf 4) fullAccess),
       ("delete key", Action.deleteKey (pkOf 3)),
       ("delete account", Action.deleteAccount "alice.near"),
       ("stake", Action.stake oneNear (pkOf 4))] do
    let tx : Transaction := {
      signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "wrap.near"
      actions := [.transfer oneNear, action] }
    let attempt := Near.apply cfg World.ap (fun _ => code) genesis [tx] []
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
  let createResult := Near.apply cfg World.ap (fun _ => code) genesis [createTx] []
  check r "account creation grants authority for subsequent key and code actions"
    (createResult.issue.isNone && createResult.outcomes.all (fun (_, o) => o.status.isSuccess) &&
      createResult.state.accessKey? created (pkOf 4) == some fullAccess &&
      ((createResult.state.account? created).bind (·.code)).isSome)

  let multiTransfer : Transaction := {
    signerId := "alice.near", publicKey := pkOf 1, nonce := 1
    receiverId := String.ofList (List.replicate 64 'a')
    actions := [.transfer oneNear, .addKey (pkOf 4) fullAccess] }
  let invalidImplicit := Near.apply cfg World.ap (fun _ => code) genesis [multiTransfer] []
  check r "implicit creation cannot be followed by an attacker-controlled key"
    ((invalidImplicit.state.account? multiTransfer.receiverId).isNone &&
      invalidImplicit.outcomes.any fun (_, o) => !o.status.isSuccess)

  -- An unsupported operation invalidates the model attempt, not the contract.
  -- A preceding successful transfer in the same apply must not be committed.
  let unsupportedModule ← match Decoder.Wat.decode
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
    signerId := "alice.near", publicKey := pkOf 1, nonce := 2, receiverId := "wrap.near"
    actions := [.functionCall "test" [] (tgas 50) oneNear] }
  let stopped := Near.apply cfg World.ap (fun _ => unsupportedCode) unsupportedState
    [transferTx, unsupportedTx] []
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

  let stakedState := genesis.setAccount "wrap.near"
    { genesisAccount (10 * oneNear) with locked := oneNear }
  let unstakeTx : Transaction := {
    signerId := "wrap.near", publicKey := pkOf 3, nonce := 1, receiverId := "wrap.near"
    actions := [.stake 0 (pkOf 3)] }
  let unstake := Near.apply cfg World.ap (fun _ => code) stakedState [unstakeTx] []
  check r "unstaking explicitly requires unmodelled epoch semantics"
    ((unstake.issue.map (·.2)) == some (.unsupportedAction "unstake (epoch machinery)"))
  check r "unsupported unstaking leaves locked funds untouched"
    ((unstake.state.account? "wrap.near").map (·.locked) == some oneNear)

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
    (w.outcomes.any fun (_, o) => o.executorId == "alice.near" && o.status.isSuccess && o.gasBurnt == 0)
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
  let implicitAtHeight := Near.apply cfg { World.ap with blockHeight := 7 } (fun _ => code) genesis [implicitTx] []
  check r "implicit key nonce begins in the creation block's nonce range"
    ((implicitAtHeight.state.accessKey? implicit implicitPk).map (·.nonce) == some 6_000_000)
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
  let r1 := Near.apply w'.cfg { World.ap with gasLimit := some 1 } (fun _ => w'.code) w'.state [tx1, tx2] w'.pending
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
  let sponsorModule ← match Decoder.Wat.decode "(module\n (import \"env\" \"promise_batch_create\" (func $batch (param i64 i64) (result i64)))\n (import \"env\" \"promise_batch_action_function_call\" (func $call (param i64 i64 i64 i64 i64 i64 i64)))\n (import \"env\" \"promise_batch_action_transfer\" (func $transfer (param i64 i64)))\n (import \"env\" \"panic\" (func $panic))\n (memory 1)\n (data (i32.const 0) \"alice.near\")\n (data (i32.const 16) \"go\")\n (data (i32.const 64) \"\\01\")\n (data (i32.const 80) \"\\02\")\n (func (export \"one\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call)\n (func (export \"twice\") (local i64) i64.const 10 i64.const 0 call $batch local.set 0 local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call)\n (func (export \"zero\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 96 i64.const 0 call $call)\n (func (export \"two\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 80 i64.const 0 call $call)\n (func (export \"transfer\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 64 call $transfer)\n (func (export \"empty\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 0 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call)\n (func (export \"panic\") (local i64) i64.const 10 i64.const 0 call $batch i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call call $panic)\n (func (export \"late_failure\") (local i64) i64.const 10 i64.const 0 call $batch local.set 0 local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 64 i64.const 0 call $call local.get 0 i64.const 2 i64.const 16 i64.const 0 i64.const 0 i64.const 80 i64.const 0 call $call)\n)\n" with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"sponsorship fixture: {e}")
  let sponsorCode : ContractCode := { module := sponsorModule, size := 0, hash := "sponsor" }
  let sponsorState (usage : Nat) := genesis.setAccount "wrap.near"
    { amount := 0, storageUsage := usage, code := some sponsorCode }
  let sponsorTx (actions : List Action) : Transaction :=
    { signerId := "alice.near", publicKey := pkOf 1, nonce := 1, receiverId := "wrap.near", actions }
  let sponsorCall (method : String) : Action := .functionCall method [] (tgas 100) 0
  let fundedTotal := (sponsorState 770).totalBalance
  let sponsored := Near.apply cfg World.ap (fun _ => sponsorCode) (sponsorState 770)
    [sponsorTx [sponsorCall "twice"]] []
  check r "sponsorship: two grants commit at storage exemption boundary"
    (sponsored.issue.isNone && sponsored.subsidizedAmount == 2 &&
     sponsored.outcomes.any fun (_, o) => o.executorId == "wrap.near" && o.status.isSuccess)
  let outgoingFunds := (sponsored.outgoing.map fun receipt =>
    match receipt.receipt with
    | .action action => Fees.totalDeposit action.actions +
        (cfg.fees.actionFees.newActionReceipt.execution +
         Fees.totalExec cfg.fees.actionFees receipt.receiverId action.actions +
         Fees.totalPrepaid action.actions) * action.gasPrice
    | .data _ => 0).sum
  check r "sponsorship: minted funds enter conservation accounting"
    (sponsored.state.totalBalance + outgoingFunds + sponsored.tokensBurnt == fundedTotal + sponsored.subsidizedAmount)
  for (name, actions, usage) in
      [("VM panic", [sponsorCall "panic"], 770),
       ("later action failure", [sponsorCall "one", .deleteKey (pkOf 99)], 770),
       ("later VM failure", [sponsorCall "one", sponsorCall "panic"], 770),
       ("storage staking failure", [sponsorCall "one"], 771)] do
    let result := Near.apply cfg World.ap (fun _ => sponsorCode) (sponsorState usage)
      [sponsorTx actions] []
    check r s!"sponsorship: {name} rolls back committed mint and promises"
      (result.issue.isNone && result.subsidizedAmount == 0 &&
       !(result.outgoing.any fun receipt => !receipt.isRefund && Fees.totalDeposit receipt.actions > 0) &&
       result.outcomes.any fun (_, o) => o.executorId == "wrap.near" && !o.status.isSuccess)

  let twoSponsorState := (sponsorState 770).setAccount "bob.near"
    { amount := 0, storageUsage := 770, code := some sponsorCode }
  let secondSponsor := { sponsorTx [sponsorCall "one"] with nonce := 2, receiverId := "bob.near" }
  let twoSponsored := Near.apply cfg World.ap (fun _ => sponsorCode) twoSponsorState
    [sponsorTx [sponsorCall "one"], secondSponsor] []
  check r "sponsorship: apply accumulates grants from separate receipts"
    (twoSponsored.issue.isNone && twoSponsored.subsidizedAmount == 2)
  let issueState := (sponsorState 770).setAccount "bob.near"
    { amount := 0, storageUsage := 770, code := some unsupportedCode }
  let issueTx := { secondSponsor with actions := [sponsorCall "test"] }
  let issueAfterGrant := Near.apply cfg World.ap (fun _ => sponsorCode) issueState
    [sponsorTx [sponsorCall "one"], issueTx] []
  check r "sponsorship: later model issue discards all earlier grants"
    (issueAfterGrant.issue.isSome && issueAfterGrant.subsidizedAmount == 0 &&
     issueAfterGrant.outgoing.isEmpty && issueAfterGrant.outcomes.isEmpty &&
     issueAfterGrant.tokensBurnt == 0 && issueAfterGrant.state.nextId == issueState.nextId)

  let s ← r.get
  IO.println s!"{s.passed} passed, {s.failed} failed"
  return (if s.failed = 0 then 0 else 1)
