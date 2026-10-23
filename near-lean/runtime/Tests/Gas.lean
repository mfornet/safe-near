import NearRuntime
import Wasm.Wat

namespace NearRuntime.Tests.Gas

open Wasm Wasm.Near Near

private def require (count : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError s!"FAIL: {name}")
  count.modify (· + 1)
  IO.println s!"ok: {name}"

private def pk : PublicKey :=
  0 :: List.replicate 32 1

private def allowance (s : ChainState) : Option Nat := do
  let key ← s.accessKey? "alice.near" pk
  match key.permission with
  | .functionCall value _ _ =>
    value
  | _ =>
    none

/-- Refunds restore the current key on delivery, and system execution consumes
chunk capacity without charging gas tokens. Tests use actual runtime transitions. -/
def run (cfg : RuntimeConfig) : IO Nat := do
  let checks ← IO.mkRef 0
  let module ← Wat.compile! "(module (func (export \"ping\")))"
  let code : ContractCode := { module, size := 0, hash := "refund-fixture" }
  let initialAllowance := 5 * 10 ^ 24
  let access : AccessKey :=
    { nonce := 0
      permission := .functionCall (some initialAllowance) "bob.near" ["ping"] }
  let initial : ChainState :=
    { accounts :=
        [("alice.near", { amount := 100 * 10 ^ 24, storageUsage := 182 }),
          ("bob.near", { amount := 10 * 10 ^ 24, storageUsage := 182, code := some code })]
      accessKeys := [(("alice.near", pk), access)] }
  let ap : ApplyState := { gasPrice := 10 ^ 8 }
  let transaction : Transaction :=
    { signerId := "alice.near"
      publicKey := pk
      nonce := 1
      receiverId := "bob.near"
      actions := [.functionCall "ping" [] (50 * 10 ^ 12) 0] }
  let submitted := Near.apply cfg ap (fun _ => code) initial [transaction] []
  let delivered := Near.apply cfg ap (fun _ => code) submitted.state [] submitted.outgoing
  let refundAmount := (delivered.outgoing.map fun r => Fees.totalDeposit r.actions).sum
  require checks "gas purchase reserves the configured minimum before delivery"
      (submitted.issue.isNone &&
        submitted.outgoing.all fun r =>
          match r.receipt with
          | .action a => a.gasPrice == max ap.gasPrice cfg.minGasPurchasePrice
          | _ => false)
  require checks "gas refund retains the signer key and is delivered separately"
      (delivered.issue.isNone && refundAmount > 0 && delivered.outgoing.length == 1 &&
        delivered.outgoing.all fun r =>
          r.isRefund && r.receiverId == "alice.near" &&
            match r.receipt with
            | .action a => a.signerId == "alice.near" && a.signerPublicKey == pk
            | _ => false)
  let refunded := Near.apply cfg ap (fun _ => code) delivered.state [] delivered.outgoing
  let spent := initialAllowance - (allowance submitted.state).getD initialAllowance
  require checks "allowance is restored only when the refund arrives"
      (allowance delivered.state == allowance submitted.state &&
        allowance refunded.state == some (initialAllowance - spent + refundAmount))
  require checks "system gas refunds report execution gas and zero burnt tokens"
      (refunded.tokensBurnt == 0 && refunded.outcomes.length == 1 &&
        refunded.outcomes.all fun (_, outcome) => outcome.gasBurnt > 0 && outcome.tokensBurnt == 0)
  let replaced :=
    delivered.state.setAccessKey "alice.near" pk
      { access with permission := .functionCall (some (2 ^ 128 - 2)) "other.near" [] }
  let saturated := Near.apply cfg ap (fun _ => code) replaced [] delivered.outgoing
  require checks "gas refunds saturate the current replacement key allowance"
      (allowance saturated.state == some (2 ^ 128 - 1))
  let removed := delivered.state.removeAccessKey "alice.near" pk
  let absentKey := Near.apply cfg ap (fun _ => code) removed [] delivered.outgoing
  require checks "gas refunds do not recreate a deleted access key"
      ((absentKey.state.accessKey? "alice.near" pk).isNone && absentKey.issue.isNone)
  let vanished := delivered.state.removeAccount "alice.near"
  let failedRefund := Near.apply cfg ap (fun _ => code) vanished [] delivered.outgoing
  require checks "failed gas refunds burn their deposit outside the outcome gas tokens"
      (failedRefund.issue.isNone && failedRefund.tokensBurnt == refundAmount &&
        failedRefund.outgoing.isEmpty &&
        failedRefund.outcomes.length == 1 &&
        failedRefund.outcomes.all fun (_, outcome) =>
          !outcome.status.isSuccess && outcome.gasBurnt > 0 && outcome.tokensBurnt == 0)
  let zeroKey : PublicKey := 0 :: List.replicate 32 0
  let balanceState := initial.setAccessKey "alice.near" zeroKey access
  let (balanceRefund, next) := refundReceipt balanceState "alice.near" 7
  let (secondRefund, next) := refundReceipt next "alice.near" 9
  let paid := Near.apply cfg ap (fun _ => code) next [] [balanceRefund]
  require checks "balance refunds never restore function-call key allowances"
      (paid.state.accessKey? "alice.near" zeroKey == some access &&
        (paid.state.account? "alice.near").map (·.amount) == some (100 * 10 ^ 24 + 7))
  let limited :=
    Near.apply cfg { ap with gasLimit := some 1 } (fun _ => code) next []
      [balanceRefund, secondRefund]
  require checks "system refund gas counts toward the chunk execution limit"
      (limited.outcomes.length == 1 && limited.state.delayed.length == 1)
  return ← checks.get

end NearRuntime.Tests.Gas
