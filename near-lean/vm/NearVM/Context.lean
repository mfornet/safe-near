import NearVM.State
import NearVM.Config
import NearVM.AccountId

/-!
# `VMContext`: the input of one function call

Mirrors `near_vm_runner::logic::VMContext`. The runtime fills it from the
receipt and the account; the Rust shim fills it from nearcore's own struct.
`toNearState` is where it becomes the host state the interpreter threads.
-/

namespace Wasm.Near

abbrev Bytes := List UInt8

/-- A view call's configuration: only the gas limit matters. -/
structure ViewConfig where
  maxGasBurnt : Nat
  deriving Repr, Inhabited

structure VMContext where
  currentAccountId : Bytes
  signerAccountId : Bytes
  signerAccountPk : Bytes
  predecessorAccountId : Bytes
  input : Bytes
  /-- Results of the promises this receipt waited on (callbacks only). -/
  promiseResults : List PromiseResult := []
  blockHeight : Nat := 0
  blockTimestamp : Nat := 0
  epochHeight : Nat := 0
  accountBalance : Nat := 0
  accountLockedBalance : Nat := 0
  storageUsage : Nat := 0
  attachedDeposit : Nat := 0
  prepaidGas : Nat := 0
  randomSeed : Bytes := []
  viewConfig : Option ViewConfig := none
  /-- Accounts whose pending receipts wait for this call's result. -/
  outputDataReceivers : List Bytes := []
  deriving Inhabited

namespace VMContext

def isView (ctx : VMContext) : Bool := ctx.viewConfig.isSome

/-- The host state at the start of the call, with the contract storage
installed and gas limits set. As in `VMLogic::new`, the balance the contract
sees (and returns in the outcome) already includes the attached deposit. -/
def toNearState (cfg : RuntimeConfig) (ctx : VMContext)
    (storage : List (Bytes × Bytes)) : NearState :=
  let maxBurnt := match ctx.viewConfig with
    | some v => v.maxGasBurnt
    | none => cfg.wasm.limits.maxGasBurnt
  { context := {
      currentAccountId := ctx.currentAccountId
      predecessorAccountId := ctx.predecessorAccountId
      signerAccountId := ctx.signerAccountId
      signerAccountPk := ctx.signerAccountPk
      input := ctx.input
      isView := ctx.isView
      blockIndex := UInt64.ofNat ctx.blockHeight
      blockTimestamp := UInt64.ofNat ctx.blockTimestamp
      epochHeight := UInt64.ofNat ctx.epochHeight
      storageUsage := UInt64.ofNat ctx.storageUsage
      accountBalance := ctx.accountBalance + ctx.attachedDeposit
      accountLockedBalance := ctx.accountLockedBalance
      attachedDeposit := ctx.attachedDeposit
      prepaidGas := UInt64.ofNat ctx.prepaidGas
      usedGas := 0 }
    storage := fun k => (storage.find? (·.1 == k)).map (·.2)
    storageKeys := storage.map (·.1)
    promiseResults := ctx.promiseResults
    config := {
      maxRegisterLen := some cfg.wasm.limits.maxRegisterSize
      maxReturnLen := some cfg.wasm.limits.maxLengthReturnedData
      maxLogLen := some cfg.wasm.limits.maxTotalLogLength
      maxNumberLogs := some cfg.wasm.limits.maxNumberLogs
      maxStorageKeyLen := some cfg.wasm.limits.maxLengthStorageKey
      maxStorageValueLen := some cfg.wasm.limits.maxLengthStorageValue
      maxInputDataDependencies := some cfg.wasm.limits.maxNumberInputDataDependencies
      oneYoctoOnPromise := cfg.wasm.oneYoctoOnPromise
      maxPromises := some cfg.wasm.limits.maxPromisesPerFunctionCallAction
      validAccountId := if cfg.wasm.limits.accountIdValidityRulesVersion == 2 then validAccountIdBytes
        else fun _ => true }
    randomSeed := ctx.randomSeed
    gas := { prepaid := ctx.prepaidGas, maxBurnt := maxBurnt }
    extCosts := cfg.wasm.extCosts
    fees := cfg.fees.actionFees
    outputDataReceivers := ctx.outputDataReceivers }

end VMContext

end Wasm.Near
