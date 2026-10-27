import Skeleton.Module

/-!
# Independent walking-module model

The step below describes byte storage and deterministic resource failures
without invoking the interpreter. Gas is an explicit parameter: establishing
a sound bound and proving this model refines the runtime remain M2 obligations.
`maxNumberRegisters` is intentionally absent because the current interpreter
does not enforce it (the executable harness pins that known limitation).
-/
namespace WNear.Skeleton
open Wasm Wasm.Near NearInterface

abbrev Storage := List (Near.Bytes × Near.Bytes)

/-- Resource checks in the order the module encounters them. -/
def modelStep (ctx : Context) (st : Option Storage) (_ : Unit) :
    StepResult Failure Storage Near.Bytes Empty := Id.run do
  let limits := ctx.protocol.wasm.limits
  let n := ctx.args.length
  let fail (failure : Failure) (logs : List String := []) :
      StepResult Failure Storage Near.Bytes Empty := .error ⟨.panic failure, logs⟩
  if limits.maxRegisterSize < n then
    return fail (.panic "input: register size exceeded")
  if limits.maxLengthStorageKey < 1 then
    return fail (.other (HostError.keyLengthExceeded 1 limits.maxLengthStorageKey).message)
  if limits.maxLengthStorageValue < n then
    return fail (.other (HostError.valueLengthExceeded n limits.maxLengthStorageValue).message)
  if limits.maxNumberLogs = 0 then
    return fail (.other (HostError.numberOfLogsExceeded 0).message)
  if limits.maxTotalLogLength < 5 then
    return fail (.other (HostError.totalLogLengthExceeded 5 limits.maxTotalLogLength).message)
  if limits.maxLengthReturnedData < n then
    return fail (.other (HostError.returnedValueLengthExceeded n limits.maxLengthReturnedData).message)
      ["saved"]
  let storage := st.getD []
  let updated := savedStorage storage ctx.args
  let usage := ctx.storageUsage - storageUsageOf ctx.protocol storage.toFinset +
    storageUsageOf ctx.protocol updated.toFinset
  let deficit := stakeDeficit ctx.protocol usage (ctx.balance + ctx.attached) ctx.locked
  if 0 < deficit then
    return fail (.lackBalanceForState deficit) ["saved"]
  return .ok { state := updated, ret := ctx.args, logs := ["saved"], promises := [] }

/-- The cost contract is supplied separately, never inferred from execution. -/
def model (gasBound : Context → Option Storage → Unit → Nat) : ContractModel where
  State := Storage
  Call := Unit
  Ret := Near.Bytes
  Panic := Failure
  Promise := Empty
  encodeState := List.toFinset
  Inv := fun storage => (storage.map Prod.fst).Nodup
  Parses := fun method _ _ => method = "save"
  encodeRet := .value
  encodeReceipts := fun _ _ => []
  panicFailure := id
  step := modelStep
  gas := gasBound

/-- The method parser has no ambiguity and accepts arbitrary input bytes. -/
theorem model_parsesFunctional (gasBound : Context → Option Storage → Unit → Nat) :
    (model gasBound).ParsesFunctional := by
  intro _ _ c c' _ _
  cases c
  cases c'
  rfl

/-- The executable success checker is precisely the interface postcondition. -/
theorem matchesCheck_iff (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (storage : Storage) (r : Observation) :
    matchesCheck ctx storage r = true ↔
      Matches (model gasBound) ctx storage.toFinset r (.ok {
        state := savedStorage storage ctx.args, ret := ctx.args,
        logs := ["saved"], promises := [] }) := by
  cases hout : r.outcome with
  | error failure => simp [matchesCheck, Matches, model, hout]
  | ok ret =>
    cases ret <;> simp [matchesCheck, Matches, model, hout, receiptDeposits, and_assoc]

end WNear.Skeleton
