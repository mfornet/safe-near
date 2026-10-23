import NearRuntime
import Wasm.Wat

/-! Decoder failures at the external code boundary must never become ordinary
contract failures or deployable empty modules. These checks exercise `apply`,
including code deployed by a running contract rather than by a transaction. -/

namespace NearRuntime.Tests.Decoder

open Wasm Wasm.Near Near

private def decode (wat : String) : IO Module := do
  match ← Wat.compile wat with
  | .ok m => pure m
  | .error e => throw (IO.userError s!"decoder test fixture: {e}")

private def require (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError s!"FAIL: {name}")
  IO.println s!"ok: {name}"

private def pk : PublicKey :=
  0 :: List.replicate 32 1

private def unavailable : ExecutionIssue :=
  .interpreterError "external code decoder unavailable"

private def state (code : ContractCode) : ChainState :=
  ({} : ChainState).setAccount "alice.near"
        { amount := 100 * 10 ^ 24, storageUsage := 182, code := some code } |>.setAccessKey
      "alice.near" pk { nonce := 0, permission := .fullAccess } |>.setContractStorage
    "alice.near" [([1], [2])]

private def tx (actions : List Action) : Transaction :=
  { signerId := "alice.near"
    publicKey := pk
    nonce := 1
    receiverId := "alice.near"
    actions }

private def atomic (before : ChainState) (after : ApplyResult) : Bool :=
  after.issue.map (·.2) == some unavailable && after.outcomes.isEmpty && after.outgoing.isEmpty &&
    after.tokensBurnt == 0 &&
    after.state.totalBalance == before.totalBalance &&
    after.state.accessKeys == before.accessKeys &&
    after.state.storage == before.storage &&
    after.state.nextId == before.nextId &&
    (after.state.account? "alice.near").map (fun a => (a.storageUsage, a.code.map (·.hash))) ==
      (before.account? "alice.near").map (fun a => (a.storageUsage, a.code.map (·.hash)))

/-- Returns the number of successful assertions; a failure aborts the suite. -/
def run (cfg : RuntimeConfig) : IO Nat := do
  let module ← decode "(module (func (export \"ok\")))"
  let known : ContractCode := { module, size := 8, hash := "known-fixture" }
  let missing : ContractCode :=
    { known with
      hash := "missing-fixture", decodeIssue := some unavailable }
  let st := state known
  let deploy :=
    Near.apply cfg {} (fun _ => missing) st
      [tx [.transfer 7, .deployContract missing, .functionCall "nonexistent" [] (50 * 10 ^ 12) 0]]
      []
  require "missing transaction decoder rejects the apply atomically" (atomic st deploy)
  let loaded := state missing
  let call :=
    Near.apply cfg {} (fun _ => missing) loaded
      [tx [.functionCall "nonexistent" [] (50 * 10 ^ 12) 0]] []
  require "missing loaded code is an issue before method lookup" (atomic loaded call)
  let producer ←
    decode
        "(module
    (import \"env\" \"promise_batch_create\" (func $create (param i64 i64) (result i64)))
    (import \"env\" \"promise_batch_action_deploy_contract\" (func $deploy (param i64 i64 i64)))
    (memory 1)
    (data (i32.const 0) \"alice.near\")
    (data (i32.const 32) \"\\00asm\\01\\00\\00\\00\")
    (func (export \"deploy\")
      i64.const 10 i64.const 0 call $create
      i64.const 8 i64.const 32 call $deploy))"
  let producerCode : ContractCode := { module := producer, size := 0, hash := "producer-fixture" }
  let producerState := state producerCode
  let invocation := tx [.functionCall "deploy" [] (100 * 10 ^ 12) 0]
  let promise := Near.apply cfg {} (fun _ => missing) producerState [invocation] []
  require "missing promise decoder rejects its producer apply atomically"
      (atomic producerState promise)
  let expectedBytes : Near.Bytes := [0, 97, 115, 109, 1, 0, 0, 0]
  let table := fun bytes => if bytes == expectedBytes then known else missing
  let scheduled := Near.apply cfg {} table producerState [invocation] []
  require "known promise code still schedules a deployment"
      (scheduled.issue.isNone &&
        scheduled.outgoing.any fun receipt =>
          receipt.actions.any fun action =>
            match action with
            | .deployContract code => code.hash == known.hash && code.decodeIssue.isNone
            | _ => false)
  let delivered := Near.apply cfg {} table scheduled.state [] scheduled.outgoing
  let deployedHash := ((delivered.state.account? "alice.near").bind (·.code)).map (·.hash)
  require "known promise deployment updates the receiving account"
      (delivered.issue.isNone && deployedHash == some known.hash)
  return 5

end NearRuntime.Tests.Decoder
