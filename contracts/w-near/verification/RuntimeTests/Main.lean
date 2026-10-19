import Spec.RuntimeInstance
import Interpreter.Wasm.Decoder.Wat

open WNear Wasm Wasm.Near

def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name}")
  IO.println s!"ok: {name}"

def bytes (s : String) : List UInt8 := s.toUTF8.toList

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
    (!(observationsValid { chained with returnData := .receiptIndex 0 }))
  check "an invalid returned receipt index is rejected"
    (!(observationsValid { base with returnData := .receiptIndex 9 }))

  -- Carry the real VM resources across calls to the deployed wNEAR module.
  let cfg ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let wat ← IO.FS.readFile "../../../near-lean/vm/tests/fixtures/w_near.wat"
  let code ← match Decoder.Wat.decode wat with
    | .ok code => pure code
    | .error error => throw (IO.userError error)
  let codeSize := (← IO.FS.readBinFile "../contract.wasm").size
  let wrap : AccountId := ⟨"wrap.near", by decide⟩
  let alice : AccountId := ⟨"alice.near", by decide⟩
  let env : Env := {
    currentAccount := wrap, predecessor := alice
    attachedDeposit := 0, prepaidGas := 300 * 10^12, promiseResult := none }
  let resources : ExecutionResources := { balance := 100 * 10^24, storageUsage := 150_000 }
  let execute := fun raw resources env call =>
    let input := mkInput resources env call
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
