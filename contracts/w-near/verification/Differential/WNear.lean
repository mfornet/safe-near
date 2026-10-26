import Spec.Contract
import Differential.Runner

/-!
# wNEAR as an executable model for scenarios

The same definitions `wnear` is built from (`Call.decode` is the graph of
`Parses`), so a scenario runs exactly the model `refines_wnear` is about.

A scenario's `state` is `null` (no contract state yet) or
`{"accounts": {"alice.near": "10", ...}, "totalSupply": ..., "accountStorageUsage": ...}`;
the last two default to the sum of the balances and the measured usage, and
can be set to build states that break the invariant (the runner then refuses
the scenario: `Refines` assumes it).
-/

namespace WNear.Scenarios

open Lean NearInterface Scenario

def modelAccount (s : String) : Except String WNear.AccountId :=
  if h : isValidAccountId s = true then pure ⟨s, h⟩ else throw s!"invalid account id {s}"

def stateOf (cfg : Config) (j : Json) : Except String (Option State × List (RawBytes × RawBytes)) := do
  if j matches .null then return (none, [])
  let accounts ← match field? j "accounts" with
    | some (.obj kvs) => kvs.toList.mapM fun (k, v) => do pure (← modelAccount k, ← natOf v)
    | none => pure []
    | some v => throw s!"accounts: expected an object, got {v.compress}"
  let sum := (accounts.map (·.2)).sum
  let s : State :=
    { registered := (accounts.map (·.1)).toFinset
      balance := fun a => ((accounts.find? (·.1 == a)).map (·.2)).getD 0
      totalSupply := ← natD j "totalSupply" sum
      accountStorageUsage := ← natD j "accountStorageUsage" cfg.measuredAccountStorageUsage }
  let records := (stateKey, header s) :: accounts.map fun (a, b) => (accountKey a, Borsh.u128 b)
  pure (some s, records)

/-- The decidable part of `Inv`. Balances of unregistered accounts are zero
by construction: scenario states give none, and the model keeps it so. -/
def invViolation (cfg : Config) (s : State) : Option String :=
  if !decide (∀ a ∈ s.registered, s.balance a < u128Bound) then some "a balance is ≥ 2^128"
  else if !decide (s.totalSupply < u128Bound) then some "total supply ≥ 2^128"
  else if s.supply != s.totalSupply then some s!"sum of balances {s.supply} ≠ total supply {s.totalSupply}"
  else if s.accountStorageUsage != cfg.measuredAccountStorageUsage then
    some s!"account storage usage {s.accountStorageUsage} is not the measured {cfg.measuredAccountStorageUsage}"
  else none

def model (protocol : Wasm.Near.RuntimeConfig) : ExecModel where
  State := State
  Call := Call
  Ret := Ret
  Panic := Panic
  Promise := Promise
  decode := Call.decode
  step := contractStep
  gas ctx _ c := gasBound ctx c
  encodeState := encode
  encodeRet := encodeRet
  encodeReceipts _ := encodeReceipts
  failure := ContractModel.ModelFailure.toFailure (wnear (Config.ofRuntime protocol))
  invViolation := invViolation (Config.ofRuntime protocol)
  initial := stateOf (Config.ofRuntime protocol)
  callName c := clip ((repr c).pretty 1000) 300

end WNear.Scenarios
