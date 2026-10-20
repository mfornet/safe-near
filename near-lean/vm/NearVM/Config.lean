import Lean.Data.Json
import NearVM.Gas

/-!
# Runtime configuration

`RuntimeConfig` holds the protocol parameters the VM and the runtime read:
gas costs of host functions, action fees, limits, storage pricing. It is
loaded from the JSON files in `configs/` (nearcore's `RuntimeConfigView`,
one file per protocol version at which parameters changed, produced by
`tools/dump-runtime-config`), never hand-copied.
-/

namespace Wasm.Near

open Lean

/-- `near_parameters::vm::LimitConfig`, the fields the runtime consults. -/
structure LimitConfig where
  maxGasBurnt : Nat
  initialMemoryPages : Nat := 1024
  maxMemoryPages : Nat := 2048
  maxNumberLogs : Nat
  maxTotalLogLength : Nat
  maxTotalPrepaidGas : Nat
  maxActionsPerReceipt : Nat
  maxNumberBytesMethodNames : Nat
  maxLengthMethodName : Nat
  maxArgumentsLength : Nat
  maxLengthReturnedData : Nat
  maxContractSize : Nat
  maxTransactionSize : Nat
  maxLengthStorageKey : Nat
  maxLengthStorageValue : Nat
  maxPromisesPerFunctionCallAction : Nat
  maxNumberInputDataDependencies : Nat
  maxRegisterSize : Nat
  maxNumberRegisters : Nat
  registersMemoryLimit : Nat
  accountIdValidityRulesVersion : Nat
  deriving Repr, Inhabited

/-- `near_parameters::vm::Config`. -/
structure WasmConfig where
  extCosts : ExtCosts
  growMemCost : Nat
  regularOpCost : Nat
  linearOpBaseCost : Nat := 0
  linearOpUnitCost : Nat := 0
  /-- Grant a one-yocto function-call deposit when liquid balance is zero. -/
  oneYoctoOnPromise : Bool := false
  ethImplicitAccounts : Bool := false
  /-- Whether method-resolution failures retain the contract-loading charge. -/
  fixContractLoadingCost : Bool := false
  limits : LimitConfig
  deriving Inhabited

/-- `near_parameters::RuntimeFeesConfig`. -/
structure FeesConfig where
  actionFees : ActionFees
  /-- Fraction of burnt gas paid to the validator, as (numerator, denominator). -/
  burntGasReward : Nat × Nat
  gasRefundPenalty : Nat × Nat := (0, 1)
  minGasRefundPenalty : Nat := 0
  pessimisticGasPriceInflation : Nat × Nat
  numBytesAccount : Nat
  numExtraBytesRecord : Nat
  deriving Repr, Inhabited

structure AccountCreationConfig where
  minAllowedTopLevelAccountLength : Nat
  registrarAccountId : String
  deriving Repr, Inhabited

structure RuntimeConfig where
  strictNonceEnabled : Bool := false
  accountCostIncrease : Bool := true
  minGasPurchasePrice : Nat := 0
  accountCreationCharge : Nat := 0
  storageAmountPerByte : Nat
  fees : FeesConfig
  wasm : WasmConfig
  accountCreation : AccountCreationConfig
  deriving Inhabited

namespace RuntimeConfig

private def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing key {k}"

private def nat (j : Json) (k : String) : Except String Nat := do
  let v ← field j k
  match v.getNat? with
  | .ok n => pure n
  | .error _ => .error s!"key {k} is not a natural number"

/-- Decimal string holding a `u128`. -/
private def natString (j : Json) (k : String) : Except String Nat := do
  let v ← field j k
  match v.getStr? with
  | .ok s =>
    match s.toNat? with
    | some n => pure n
    | none => .error s!"key {k} is not a decimal string"
  | .error _ => .error s!"key {k} is not a string"

private def ratio (j : Json) (k : String) : Except String (Nat × Nat) := do
  let v ← field j k
  match v.getArr? with
  | .ok #[a, b] =>
    match a.getNat?, b.getNat? with
    | .ok a, .ok b => pure (a, b)
    | _, _ => .error s!"key {k} is not a ratio"
  | _ => .error s!"key {k} is not a ratio"

private def fee (j : Json) : Except String Fee := do
  pure { sendSir := ← nat j "send_sir", sendNotSir := ← nat j "send_not_sir", execution := ← nat j "execution" }

private def feeAt (j : Json) (k : String) : Except String Fee := do fee (← field j k)

private def limits (j : Json) : Except String LimitConfig := do
  pure {
    maxGasBurnt := ← nat j "max_gas_burnt"
    initialMemoryPages := ← nat j "initial_memory_pages"
    maxMemoryPages := ← nat j "max_memory_pages"
    maxNumberLogs := ← nat j "max_number_logs"
    maxTotalLogLength := ← nat j "max_total_log_length"
    maxTotalPrepaidGas := ← nat j "max_total_prepaid_gas"
    maxActionsPerReceipt := ← nat j "max_actions_per_receipt"
    maxNumberBytesMethodNames := ← nat j "max_number_bytes_method_names"
    maxLengthMethodName := ← nat j "max_length_method_name"
    maxArgumentsLength := ← nat j "max_arguments_length"
    maxLengthReturnedData := ← nat j "max_length_returned_data"
    maxContractSize := ← nat j "max_contract_size"
    maxTransactionSize := ← nat j "max_transaction_size"
    maxLengthStorageKey := ← nat j "max_length_storage_key"
    maxLengthStorageValue := ← nat j "max_length_storage_value"
    maxPromisesPerFunctionCallAction := ← nat j "max_promises_per_function_call_action"
    maxNumberInputDataDependencies := ← nat j "max_number_input_data_dependencies"
    maxRegisterSize := ← nat j "max_register_size"
    maxNumberRegisters := ← nat j "max_number_registers"
    registersMemoryLimit := ← nat j "registers_memory_limit"
    accountIdValidityRulesVersion := ← nat j "account_id_validity_rules_version" }

private def extCosts (j : Json) : Except String ExtCosts := do
  match j with
  | .obj kvs =>
    let mut table : List (String × Nat) := []
    for (k, v) in kvs.toArray do
      match v.getNat? with
      | .ok n => table := (k, n) :: table
      | .error _ => throw s!"ext cost {k} is not a natural number"
    let arr := table.toArray
    pure { lookup := fun name => (arr.find? (·.1 == name)).map (·.2) |>.getD 0 }
  | _ => .error "ext_costs is not an object"

/-- Parse nearcore's `RuntimeConfigView` JSON. -/
def ofJson (j : Json) : Except String RuntimeConfig := do
  let tc ← field j "transaction_costs"
  let ac ← field tc "action_creation_config"
  let addKey ← field ac "add_key_cost"
  let dataReceipt ← field tc "data_receipt_creation_config"
  let storageUsage ← field tc "storage_usage_config"
  let wasm ← field j "wasm_config"
  let acc ← field j "account_creation_config"
  let actionFees : ActionFees := {
    createAccount := ← feeAt ac "create_account_cost"
    deleteAccount := ← feeAt ac "delete_account_cost"
    deployContractBase := ← feeAt ac "deploy_contract_cost"
    deployContractByte := ← feeAt ac "deploy_contract_cost_per_byte"
    functionCallBase := ← feeAt ac "function_call_cost"
    functionCallByte := ← feeAt ac "function_call_cost_per_byte"
    transfer := ← feeAt ac "transfer_cost"
    stake := ← feeAt ac "stake_cost"
    addFullAccessKey := ← feeAt addKey "full_access_cost"
    addFunctionCallKeyBase := ← feeAt addKey "function_call_cost"
    addFunctionCallKeyByte := ← feeAt addKey "function_call_cost_per_byte"
    deleteKey := ← feeAt ac "delete_key_cost"
    newActionReceipt := ← feeAt tc "action_receipt_creation_config"
    newDataReceiptBase := ← feeAt dataReceipt "base_cost"
    newDataReceiptByte := ← feeAt dataReceipt "cost_per_byte"
    delegate := ← feeAt ac "delegate_cost" }
  let finance ← field j "runtime_finance"
  pure {
    strictNonceEnabled := ← (← field (← field j "runtime_admission") "strict_nonce").getBool?
    accountCostIncrease := ← (← field finance "account_cost_increase").getBool?
    minGasPurchasePrice := ← natString j "min_gas_purchase_price"
    accountCreationCharge := ← natString j "account_creation_charge"
    storageAmountPerByte := ← natString j "storage_amount_per_byte"
    fees := {
      actionFees
      gasRefundPenalty := ← ratio finance "gas_refund_penalty"
      minGasRefundPenalty := ← nat finance "min_gas_refund_penalty"
      burntGasReward := ← ratio tc "burnt_gas_reward"
      pessimisticGasPriceInflation := ← ratio tc "pessimistic_gas_price_inflation_ratio"
      numBytesAccount := ← nat storageUsage "num_bytes_account"
      numExtraBytesRecord := ← nat storageUsage "num_extra_bytes_record" }
    wasm := {
      extCosts := ← extCosts (← field wasm "ext_costs")
      growMemCost := ← nat wasm "grow_mem_cost"
      regularOpCost := ← nat wasm "regular_op_cost"
      linearOpBaseCost := ← nat wasm "linear_op_base_cost"
      linearOpUnitCost := ← nat wasm "linear_op_unit_cost"
      ethImplicitAccounts := ← (← field wasm "eth_implicit_accounts").getBool?
      oneYoctoOnPromise := ← (← field wasm "one_yocto_on_promise").getBool?
      fixContractLoadingCost := ← (← field wasm "fix_contract_loading_cost").getBool?
      limits := ← limits (← field wasm "limit_config") }
    accountCreation := {
      minAllowedTopLevelAccountLength := ← nat acc "min_allowed_top_level_account_length"
      registrarAccountId := ← (do
        match (← field acc "registrar_account_id").getStr? with
        | .ok s => pure s
        | .error _ => throw "registrar_account_id is not a string") } }

def parse (text : String) : Except String RuntimeConfig := do
  match Json.parse text with
  | .ok j => ofJson j
  | .error e => .error s!"invalid JSON: {e}"

/-- Load `configs/runtime_config_v<version>.json` relative to `dir`. -/
def load (dir : System.FilePath) (version : Nat) : IO RuntimeConfig := do
  let path := dir / s!"runtime_config_v{version}.json"
  let text ← IO.FS.readFile path
  match parse text with
  | .ok cfg => pure cfg
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Latest protocol version with a config file in `configs/`. -/
def latestVersion : Nat := 86

end RuntimeConfig

end Wasm.Near
