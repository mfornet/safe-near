import NearVM.State
import NearVM.Config
import NearVM.AccountId

/-!
# `VMContext`: the input of one function call

Mirrors `near_vm_runner::logic::VMContext`, with an explicit external method
validation policy. The runtime fills it from the receipt and account; the
conformance shim selects the policy used by its native external adapter.
`toNearState` is where it becomes the host state the interpreter threads.
-/

namespace Wasm.Near

/-- A view call's configuration: only the gas limit matters. -/
structure ViewConfig where
  maxGasBurnt : Nat
  deriving Repr, Inhabited

structure VMContext where
  /-- External validation policy, not a protocol parameter. False matches nearcore VM mocks. -/
  validateActionMethodUtf8 : Bool := true
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
  /-- External storage policy, beyond native VMContext: RuntimeExt charges old-value
  bytes, whereas the standalone MockedExternal oracle omits these costs. -/
  chargeStorageValueAccess : Bool := false
  /-- Full chunk trie, including other accounts and runtime metadata. Callers retain
  the returned cache across calls; receipt commit/rollback is their responsibility. -/
  storageAccounting : Option _root_.Near.TrieOverlay.State := none
  storageReadsFromTrie : Bool := false
  /-- Accounts whose pending receipts wait for this call's result. -/
  outputDataReceivers : List Bytes := []
  /-- Hash of the executing action (`create_action_hash_from_receipt_id`), from which the
  data ids of this call derive; empty when the caller supplies no native identity. -/
  actionHash : Bytes := []
  /-- Native data ids of the current account's yields that have a receipt or status in state. -/
  existingYields : List Bytes := []
  /-- `chain_id` of the epoch provider. -/
  chainId : Bytes := []
  deriving Inhabited

/-- Storage keys in byte order: the order the trie iterates them in, and one
that does not depend on how the caller listed the storage. -/
def sortedKeys (storage : List (Bytes × Bytes)) : List Bytes :=
  (storage.map (·.1)).mergeSort fun a b => decide (a ≤ b)

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
      usedGas := 0
      chainId := ctx.chainId }
    actionHash := ctx.actionHash
    existingYields := ctx.existingYields
    storage := fun k => (storage.find? (·.1 == k)).map (·.2)
    storageKeys := sortedKeys storage
    storageAccounting := ctx.storageAccounting
    storageReadsFromTrie := ctx.storageReadsFromTrie
    promiseResults := ctx.promiseResults
    config := {
      chargeStorageValueAccess := ctx.chargeStorageValueAccess
      validateActionMethodUtf8 := ctx.validateActionMethodUtf8
      maxRegisterLen := some cfg.wasm.limits.maxRegisterSize
      maxReturnLen := some cfg.wasm.limits.maxLengthReturnedData
      maxLogLen := some cfg.wasm.limits.maxTotalLogLength
      maxNumberLogs := some cfg.wasm.limits.maxNumberLogs
      maxStorageKeyLen := some cfg.wasm.limits.maxLengthStorageKey
      maxStorageValueLen := some cfg.wasm.limits.maxLengthStorageValue
      maxInputDataDependencies := some cfg.wasm.limits.maxNumberInputDataDependencies
      oneYoctoOnPromise := cfg.wasm.oneYoctoOnPromise
      ethImplicitAccounts := cfg.wasm.ethImplicitAccounts
      maxPromises := some cfg.wasm.limits.maxPromisesPerFunctionCallAction
      maxContractSize := some cfg.wasm.limits.maxContractSize
      maxYieldPayloadSize := some cfg.wasm.limits.maxYieldPayloadSize
      validAccountId := if cfg.wasm.limits.accountIdValidityRulesVersion == 2 then validAccountIdBytes
        else fun _ => true }
    randomSeed := ctx.randomSeed
    gas := { prepaid := ctx.prepaidGas, maxBurnt := maxBurnt }
    extCosts := cfg.wasm.extCosts
    fees := cfg.fees.actionFees
    outputDataReceivers := ctx.outputDataReceivers }

end VMContext

end Wasm.Near
