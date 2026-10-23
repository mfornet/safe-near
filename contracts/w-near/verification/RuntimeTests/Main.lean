import Spec.RuntimeInstance
import Wasm.Wat

open WNear Wasm Wasm.Near

def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name}")
  IO.println s!"ok: {name}"

def bytes (s : String) : List UInt8 := s.toUTF8.toList

def modelOutcome (result : Except WNear.Panic WNear.Outcome) : IO WNear.Outcome :=
  match result with
  | .ok outcome => pure outcome
  | .error error => throw (IO.userError s!"unexpected model failure: {repr error}")

def main : IO Unit := do
  for message in ["plain", "a\"b\\c\n\t", "日本語 🙂", "\"msg\":\"injected\""] do
    let json := "{\"msg\":" ++ jsonString message ++ "}"
    check "JSON string round trip" (jsonField json "msg" == some message)
  check "JSON fields accept whitespace and arbitrary field order"
    (jsonField "{ \"other\" : true, \"msg\" : \"hello\" }" "msg" == some "hello")
  check "malformed JSON is rejected" ((jsonField "{\"msg\":\"unterminated}" "msg").isNone)
  check "wrong JSON value type is rejected" ((jsonField "{\"msg\":7}" "msg").isNone)
  check "invalid receiver bytes do not become a valid substitute account"
    ((accountOfBytes? (bytes "INVALID")).isNone)

  for (body, expected) in [
      ("\"0\"", some 0), ("  \"42\" \n", some 42),
      ("\"+001\"", some 1), ("\"0007\"", some 7),
      ("\"340282366920938463463374607431768211455\"", some (2^128 - 1)),
      ("\"340282366920938463463374607431768211456\"", none),
      ("42", none), ("null", none), ("\"\"", none), ("\"+\"", none),
      ("\"-0\"", none), ("\" 1\"", none), ("\"1 \"", none),
      ("\"1.0\"", none), ("\"1\" trailing", none), ("\"１２\"", none),
      ("\"\\u0037\"", some 7), ("\"\\u002B\\u0030\\u0037\"", some 7),
      (" \"7\"", none), ("\"7\" ", none), ("\"++7\"", none)] do
    check s!"callback U128 projection: {body}" (parseU128Result (bytes body) == expected)
  check "invalid UTF-8 remains a malformed successful callback"
    (callbackResultOf [.successful [255]] == some (.successful none))
  check "failed, not-ready and missing callback results remain distinct"
    (callbackResultOf [.failed] == some .failed && callbackResultOf [.notReady] == some .notReady &&
      (callbackResultOf []).isNone)
  check "typed amounts must fit Rust U128"
    (decide ((Call.nearWithdraw (2^128 - 1)).WF) && !decide ((Call.nearWithdraw (2^128)).WF))

  let transfer : ReceiptSpec := { receiverId := bytes "alice.near", actions := [.transfer 1] }
  let base : VMOutcome := { (default : VMOutcome) with receipts := [transfer] }
  check "a known transfer has a valid observation" (observationsValid base)
  let unknown : ReceiptSpec := { transfer with actions := [.createAccount] }
  check "unknown actions are rejected rather than dropped"
    (!(observationsValid { base with receipts := [transfer, unknown] }))
  check "invalid account ids are rejected rather than substituted"
    (!(observationsValid { base with receipts := [{ transfer with receiverId := bytes "INVALID" }] }))
  check "a missing dependency is rejected"
    (!(observationsValid { base with receipts := [{ transfer with dependencies := [9] }] }))
  check "a dependency join is rejected rather than flattened"
    (!(observationsValid { base with receipts := [transfer, transfer, { transfer with dependencies := [0, 1] }] }))
  check "a branched dependency cannot disappear from a linear model"
    (!(observationsValid { base with receipts := [transfer, { transfer with dependencies := [0] },
      { transfer with dependencies := [0] }] }))
  let chained : VMOutcome := { base with
    receipts := [transfer, { transfer with dependencies := [0] }]
    returnData := .receiptIndex 1 }
  check "a complete returned chain is representable" (observationsValid chained)
  check "returning the root instead of its callback is distinguished"
    (observationsValid { chained with returnData := .receiptIndex 0 } &&
      returnDataOf { chained with returnData := .receiptIndex 0 } != returnDataOf chained)
  check "an invalid returned receipt index is rejected"
    (!(observationsValid { base with returnData := .receiptIndex 9 }))

  -- Carry the real VM resources across calls to the deployed wNEAR module.
  let cfg ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let contractBytes ← IO.FS.readBinFile "../contract.wasm"
  let code ← match Wasm.Binary.decode contractBytes with
    | .ok code => pure code
    | .error error => throw (IO.userError error.message)
  let codeSize := contractBytes.size
  let wrap : AccountId := ⟨"wrap.near", by decide⟩
  let alice : AccountId := ⟨"alice.near", by decide⟩
  let env : Env := {
    currentAccount := wrap, predecessor := alice
    attachedDeposit := 0, prepaidGas := 300 * 10^12, promiseResult := none }
  let resources : ExecutionResources := { balance := 100 * 10^24, storageUsage := 150_000 }
  let rawResults : List Wasm.PromiseResult := [.successful [255, 0, 10], .failed, .notReady]
  check "all raw callback bytes and result positions reach the VM unchanged"
    ((toVMContext (mkInput resources rawResults env .ftTotalSupply)).promiseResults == rawResults)
  let execute := fun raw resources env call =>
    let input := mkInput resources [] env call
    run cfg code codeSize input.method (toVMContext input) raw
  let initialized := execute [] resources env .new
  check "resource-aware initialization succeeds" initialized.succeeded
  let deposit := execute initialized.storage
    { balance := initialized.balance, storageUsage := initialized.storageUsage }
    { env with attachedDeposit := 10^24 } .nearDeposit
  check "resource-aware deposit succeeds" deposit.succeeded
  let withdraw := execute deposit.storage
    { balance := deposit.balance, storageUsage := deposit.storageUsage }
    { env with attachedDeposit := 1 } (.nearWithdraw (10^22))
  check "funded withdrawal through the adapter succeeds" withdraw.succeeded
  check "withdrawal returns its transfer receipt rather than a unit value"
    (withdraw.returnData == .receiptIndex 0 && observationsValid withdraw &&
      returnDataOf withdraw == encodeRet (.promise 0))
  check "withdrawal accounts for attached and transferred NEAR"
    (withdraw.balance + (10^22 + 1) == deposit.balance + 1)
  check "withdrawal retains storage usage for an existing account"
    (withdraw.storageUsage == deposit.storageUsage)
  check "successful VM gas is bounded and includes reserved gas"
    (withdraw.burntGas <= withdraw.usedGas && withdraw.usedGas <= env.prepaidGas)
  let failed := execute deposit.storage
    { balance := deposit.balance, storageUsage := deposit.storageUsage }
    env (.nearWithdraw (10^22))
  check "unauthorized withdrawal restores all resources"
    (!failed.succeeded && failed.balance == deposit.balance &&
      failed.storageUsage == deposit.storageUsage && failed.storage == deposit.storage &&
      failed.receipts.isEmpty)

  let exhausted := execute deposit.storage
    { balance := deposit.balance, storageUsage := deposit.storageUsage }
    { env with attachedDeposit := 1, prepaidGas := 1 } (.nearWithdraw (10^22))
  check "out of gas also restores storage, balance, usage and receipts"
    ((exhausted.aborted.map (·.isOutOfGas)).getD false &&
      exhausted.balance == deposit.balance && exhausted.storageUsage == deposit.storageUsage &&
      exhausted.storage == deposit.storage && exhausted.receipts.isEmpty)

  -- Start each raw callback from identical VM/model transfer-call snapshots.
  let modelCfg : WNear.Config := { extraBytesPerRecord := cfg.fees.numExtraBytesRecord }
  let modelDeposit ← modelOutcome (step modelCfg (some (WNear.new modelCfg).state)
    { env with attachedDeposit := 10^24 } .nearDeposit)
  let modelWithdraw ← modelOutcome (step modelCfg (some modelDeposit.state)
    { env with attachedDeposit := 1 } (.nearWithdraw (10^22)))
  check "deployed withdrawal agrees with the model's exact returned receipt"
    (returnDataOf withdraw == encodeRet modelWithdraw.ret &&
      promisesOf withdraw == modelWithdraw.promises &&
      decide (rawOf withdraw.storage = encode modelWithdraw.state))
  let bob : AccountId := ⟨"bob.near", by decide⟩
  let registerEnv := { env with attachedDeposit := 10^22 }
  let registered := execute deposit.storage
    { balance := deposit.balance, storageUsage := deposit.storageUsage }
    registerEnv (.storageDeposit (some bob) none)
  let modelRegistered ← modelOutcome (step modelCfg (some modelDeposit.state)
    registerEnv (.storageDeposit (some bob) none))
  let transferEnv := { env with attachedDeposit := 1 }
  let transferCall := Call.ftTransferCall bob (10^22) none ""
  let transferred := execute registered.storage
    { balance := registered.balance, storageUsage := registered.storageUsage }
    transferEnv transferCall
  let modelTransferred ← modelOutcome (step modelCfg (some modelRegistered.state) transferEnv transferCall)
  check "transfer-call snapshot agrees with model storage"
    (transferred.succeeded && decide (rawOf transferred.storage = encode modelTransferred.state))
  let callback := Call.ftResolveTransfer alice bob (10^22)
  let callbackCases : List (String × List Wasm.PromiseResult) := [
    ("missing", []), ("failed", [.failed]), ("zero", [.successful (bytes "\"0\"")]),
    ("partial", [.successful (bytes "\"7\"")]),
    ("noncanonical", [.successful (bytes " \"+0007\"\n")]),
    ("escaped", [.successful (bytes "\"\\u0037\"")]),
    ("escaped plus", [.successful (bytes "\"\\u002b007\"")]),
    ("non-JSON whitespace", [.successful (bytes " \"7\"")]),
    ("overflow", [.successful (bytes "\"340282366920938463463374607431768211456\"")]),
    ("invalid UTF8", [.successful [255]]), ("numeric JSON", [.successful (bytes "7")]),
    ("trailing bytes", [.successful (bytes "\"7\" trailing")]),
    ("additional results", [.successful (bytes "\"7\""), .failed])]
  for (name, results) in callbackCases do
    let callbackEnv := { env with predecessor := wrap, promiseResult := callbackResultOf results }
    let input := mkInput
      { balance := transferred.balance, storageUsage := transferred.storageUsage }
      results callbackEnv callback
    let observed := run cfg code codeSize input.method (toVMContext input) transferred.storage
    match step modelCfg (some modelTransferred.state) callbackEnv callback with
    | .error p =>
      check s!"callback model failure and rollback: {name}"
        (!observed.succeeded && observed.storage == transferred.storage && observed.receipts.isEmpty &&
          ((observed.aborted.map fun e => decide ((e.message.splitOn p.message).length > 1)).getD false))
      check "missing callback result is a structured host error"
        (observed.aborted == some (.hostError (.invalidPromiseResultIndex 0)))
    | .ok expected =>
      check s!"raw callback matches model observations: {name}"
        (observed.succeeded && observationsValid observed &&
          decide (rawOf observed.storage = encode expected.state) &&
          decide (returnDataOf observed = WNear.encodeRet expected.ret) &&
          observed.logs == expected.logs && promisesOf observed == expected.promises &&
          observed.balance + expected.nearOut == transferred.balance)
