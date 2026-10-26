import Lean.Data.Json
import NearInterface.Gas
import NearInterface.HostCrypto

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
  maxDeployActionsPerReceipt : Nat
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
  /-- `yield_timeout_length_in_blocks`: blocks until an unresumed `promise_yield_create` times out. -/
  yieldTimeoutLengthInBlocks : Nat := 200
  /-- `max_yield_payload_size`: bytes `promise_yield_resume` accepts. -/
  maxYieldPayloadSize : Nat := 1024
  /-- `prepare_v3` limits; `none` when the protocol version does not set one. -/
  maxFunctionsNumberPerContract : Option Nat := none
  maxLocalsPerContract : Option Nat := none
  maxFunctionBodySize : Option Nat := none
  maxTablesPerContract : Option Nat := none
  maxElementsPerContractTable : Option Nat := none
  maxTypesPerContract : Option Nat := none
  /-- `max_receipt_size`, checked on the receipts a function call creates. -/
  maxReceiptSize : Nat := 2 ^ 32 - 1
  /-- `per_receipt_storage_proof_size_limit`: the storage proof one receipt may record. -/
  perReceiptStorageProofSizeLimit : Nat := 2 ^ 32 - 1
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
  /-- `eth_implicit_global_contract`: ETH-implicit accounts use the global wallet contract. -/
  ethImplicitGlobalContract : Bool := false
  /-- `bls12381_not_in_group_fix` (NEP-488): `bls12381_p1_sum` and `bls12381_p1_decompress` accept
  the points of order 3 with abscissa zero. -/
  bls12381NotInGroupFix : Bool := false
  /-- `global_contract_host_fns`: the global-contract host functions are
  linked (protocol 78 on); before, importing one fails to link. -/
  globalContractHostFns : Bool := false
  limits : LimitConfig
  deriving Inhabited

/-- `near_parameters::RuntimeFeesConfig`. -/
structure FeesConfig where
  actionFees : ActionFees
  /-- Fraction of burnt gas paid to the contract, as (numerator, denominator). -/
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
  v1TransactionsEnabled : Bool := false
  transactionSizeIncludesSignature : Bool := false
  /-- `UniqueChunkTransactions`: a repeated transaction in a chunk is skipped. -/
  uniqueChunkTransactions : Bool := false
  accountCostIncrease : Bool := true
  minGasPurchasePrice : Nat := 0
  accountCreationCharge : Nat := 0
  storageAmountPerByte : Nat
  /-- `global_contract_storage_amount_per_byte`: tokens burnt per byte of a deployed global contract. -/
  globalContractStorageAmountPerByte : Nat := 0
  /-- Compute charged for applying a distribution receipt: base plus per code byte. -/
  deployGlobalContractExecutionBase : Nat := 0
  deployGlobalContractExecutionPerByte : Nat := 0
  /-- `IncludeDeployGlobalContractOutcomeBurntStorage`: the storage cost is part of the outcome's burn. -/
  includeDeployGlobalContractOutcomeBurntStorage : Bool := false
  /-- `GlobalContractDistributionNonce`: distribution receipts carry a freshness nonce. -/
  globalContractDistributionNonce : Bool := false
  /-- `FixDeleteAccountGlobalContractStorageUsage`. -/
  fixDeleteAccountGlobalContractStorageUsage : Bool := false
  /-- `FixDelegateActionDepositWithFunctionCallError`. -/
  fixDelegateActionDepositWithFunctionCallError : Bool := false
  /-- `EnforcePerReceiptStorageProofLimit`: a receipt's proof counts from the receipt's start, not
  from the function call's. -/
  enforcePerReceiptStorageProofLimit : Bool := false
  /-- `main_storage_proof_size_soft_limit`: the chunk takes no more receipts past this proof size. -/
  mainStorageProofSizeSoftLimit : Nat := 2 ^ 32 - 1
  /-- `compute_costs.ext`: the `ExtCosts` whose compute cost differs from their gas cost. -/
  extCompute : List (String × Nat) := []
  /-- `compute_costs.action_execution`: the action execution fees whose compute cost differs from
  their gas cost. Send fees always have compute equal to gas (the parser rejects other configs). -/
  actionExecutionCompute : List (String × Nat) := []
  fees : FeesConfig
  wasm : WasmConfig
  accountCreation : AccountCreationConfig
  /-- The cryptography of the host functions, supplied by the node; not a protocol parameter. -/
  hostCrypto : Option HostCrypto := none
  deriving Inhabited

namespace RuntimeConfig

/-- The action fees with each execution fee at its compute cost (`FeeComponent::compute`). -/
def computeActionFees (cfg : RuntimeConfig) : ActionFees :=
  cfg.actionExecutionCompute.foldl (fun fees (name, compute) => (fees.setExecution name compute).getD fees)
    cfg.fees.actionFees

/-- The compute cost of the `ExtCosts` named `name`: its override, else its gas cost. -/
def extComputeCost (cfg : RuntimeConfig) (name : String) : Nat :=
  (cfg.extCompute.lookup name).getD (cfg.wasm.extCosts.cost name)

/-- `storage_removes_compute`: the compute of `count` storage removals of `keyBytes` key bytes
and `valueBytes` value bytes in all, which the runtime charges without gas. -/
def storageRemovesCompute (cfg : RuntimeConfig) (count keyBytes valueBytes : Nat) : Nat :=
  cfg.extComputeCost "storage_remove_base" * count + cfg.extComputeCost "storage_remove_key_byte" * keyBytes +
    cfg.extComputeCost "storage_remove_ret_value_byte" * valueBytes

/-- `ProfileDataV3::total_compute_usage` of one VM call: each host cost's burnt gas scaled by
its compute-to-gas ratio (rounded down per cost), plus the action and Wasm gas, whose
compute equals their gas. -/
def vmComputeUsage (cfg : RuntimeConfig) (profile : GasProfile) : Nat :=
  let ext := profile.ext.foldl (fun total (name, gas) =>
    total + match cfg.extCompute.lookup name with
      | some compute =>
        let unit := cfg.wasm.extCosts.cost name
        if unit == 0 then gas else gas * compute / unit
      | none => gas) 0
  ext + profile.actionBurnt + profile.wasm

private def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing key {k}"

private def nat (j : Json) (k : String) : Except String Nat := do
  let v ← field j k
  match v.getNat? with
  | .ok n => pure n
  | .error _ => .error s!"key {k} is not a natural number"

/-- An optional natural number: absent or `null` is `none`. -/
private def optNat (j : Json) (k : String) : Except String (Option Nat) :=
  match j.getObjVal? k with
  | .error _ | .ok .null => .ok none
  | .ok v =>
    match v.getNat? with
    | .ok n => .ok (some n)
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
    maxDeployActionsPerReceipt := ← nat j "max_deploy_actions_per_receipt"
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
    accountIdValidityRulesVersion := ← nat j "account_id_validity_rules_version"
    yieldTimeoutLengthInBlocks := (nat j "yield_timeout_length_in_blocks").toOption.getD 200
    maxYieldPayloadSize := (nat j "max_yield_payload_size").toOption.getD 1024
    maxFunctionsNumberPerContract := ← optNat j "max_functions_number_per_contract"
    maxLocalsPerContract := ← optNat j "max_locals_per_contract"
    maxFunctionBodySize := ← optNat j "max_function_body_size"
    maxTablesPerContract := ← optNat j "max_tables_per_contract"
    maxElementsPerContractTable := ← optNat j "max_elements_per_contract_table"
    maxTypesPerContract := ← optNat j "max_types_per_contract"
    maxReceiptSize := ← nat j "max_receipt_size"
    perReceiptStorageProofSizeLimit := ← nat j "per_receipt_storage_proof_size_limit" }

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

private def natTable (j : Json) (what : String) : Except String (List (String × Nat)) := do
  match j with
  | .obj kvs =>
    kvs.toArray.toList.mapM fun (k, v) => do
      match v.getNat? with
      | .ok n => pure (k, n)
      | .error _ => throw s!"{what} {k} is not a natural number"
  | _ => throw s!"{what} is not an object"

/-- `compute_costs`: compute costs that differ from gas. Absent (configs dumped before it
existed) means none. An unknown action name or a send-fee override is rejected: the model
would otherwise charge it as gas. -/
private def computeCosts (j : Json) (fees : ActionFees) :
    Except String (List (String × Nat) × List (String × Nat)) := do
  match field j "compute_costs" with
  | .error _ => pure ([], [])
  | .ok costs =>
    let ext ← natTable (← field costs "ext") "ext compute cost"
    let execution ← natTable (← field costs "action_execution") "action execution compute cost"
    let send ← natTable (← field costs "action_send") "action send compute cost"
    unless send.isEmpty do throw "action send fees with a compute cost other than gas are not modeled"
    for (name, n) in execution do
      if (fees.setExecution name n).isNone then throw s!"unknown action cost {name}"
    pure (ext, execution)

/-- Parse nearcore's `RuntimeConfigView` JSON. -/
def ofJson (j : Json) : Except String RuntimeConfig := do
  let tc ← field j "transaction_costs"
  let ac ← field tc "action_creation_config"
  let addKey ← field ac "add_key_cost"
  let dataReceipt ← field tc "data_receipt_creation_config"
  let storageUsage ← field tc "storage_usage_config"
  let wasm ← field j "wasm_config"
  let acc ← field j "account_creation_config"
  -- `RuntimeConfigView` omits the global-contract action fees. nearcore sets
  -- them in `runtime_configs/77.yaml`; the host functions that charge them are
  -- enabled from 78 (`global_contract_host_fns`) and no later version changes them.
  let hostFns := ((field wasm "global_contract_host_fns").toOption.bind (·.getBool?.toOption)).getD false
  let disabled : Fee :=
    { sendSir := 999_999_999_999_999, sendNotSir := 999_999_999_999_999, execution := 999_999_999_999_999 }
  let useGlobalBase : Fee := if hostFns then
    { sendSir := 184_765_750_000, sendNotSir := 184_765_750_000, execution := 184_765_750_000 }
    else disabled
  let useGlobalByte : Fee := if hostFns then
    { sendSir := 6_812_999, sendNotSir := 47_683_715, execution := 64_572_944 } else disabled
  -- `runtime_extra` carries what the RPC view omits (see `tools/dump-runtime-config`).
  let extra : Option Json := (field j "runtime_extra").toOption
  let extraFee (k : String) (fallback : Fee) : Except String Fee :=
    match extra with
    | none => pure fallback
    | some e => do feeAt (← field e "action_fees") k
  let extraFlag (k : String) : Bool :=
    match extra with
    | none => false
    | some e => ((field e k).toOption.bind (·.getBool?.toOption)).getD false
  let extraNat (k : String) : Nat :=
    match extra with
    | none => 0
    | some e => ((nat e k).toOption).getD 0
  let extraString (k : String) : Nat :=
    match extra with
    | none => 0
    | some e => ((natString e k).toOption).getD 0
  let useGlobalBase ← extraFee "use_global_contract_base" useGlobalBase
  let useGlobalByte ← extraFee "use_global_contract_byte" useGlobalByte
  let deployGlobalBase ← extraFee "deploy_global_contract_base" disabled
  let deployGlobalByte ← extraFee "deploy_global_contract_byte" disabled
  let gasKeyTransferBase ← extraFee "gas_key_transfer_base" disabled
  let gasKeyByte ← extraFee "gas_key_byte" disabled
  let gasKeyNonceWriteBase ← extraFee "gas_key_nonce_write_base" disabled
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
    delegate := ← feeAt ac "delegate_cost"
    useGlobalContractBase := (feeAt ac "use_global_contract_cost").toOption.getD useGlobalBase
    useGlobalContractByte :=
      (feeAt ac "use_global_contract_cost_per_identifier_byte").toOption.getD useGlobalByte
    deployGlobalContractBase := deployGlobalBase
    deployGlobalContractByte := deployGlobalByte
    gasKeyTransferBase
    gasKeyByte
    gasKeyNonceWriteBase }
  let finance ← field j "runtime_finance"
  let (computeExt, computeExecution) ← computeCosts j actionFees
  pure {
    strictNonceEnabled := ← (← field (← field j "runtime_admission") "strict_nonce").getBool?
    v1TransactionsEnabled := ← (← field (← field j "runtime_admission") "v1_transactions").getBool?
    transactionSizeIncludesSignature := ← (← field (← field j "runtime_admission") "transaction_size_includes_signature").getBool?
    uniqueChunkTransactions := ← (← field (← field j "runtime_admission") "unique_chunk_transactions").getBool?
    accountCostIncrease := ← (← field finance "account_cost_increase").getBool?
    minGasPurchasePrice := ← natString j "min_gas_purchase_price"
    accountCreationCharge := ← natString j "account_creation_charge"
    storageAmountPerByte := ← natString j "storage_amount_per_byte"
    globalContractStorageAmountPerByte := extraString "global_contract_storage_amount_per_byte"
    deployGlobalContractExecutionBase := extraNat "deploy_global_contract_execution_base"
    deployGlobalContractExecutionPerByte := extraNat "deploy_global_contract_execution_per_byte"
    includeDeployGlobalContractOutcomeBurntStorage := extraFlag "include_deploy_global_contract_outcome_burnt_storage"
    globalContractDistributionNonce := extraFlag "global_contract_distribution_nonce"
    fixDeleteAccountGlobalContractStorageUsage := extraFlag "fix_delete_account_global_contract_storage_usage"
    fixDelegateActionDepositWithFunctionCallError := extraFlag "fix_delegate_action_deposit_with_function_call_error"
    enforcePerReceiptStorageProofLimit := extraFlag "enforce_per_receipt_storage_proof_limit"
    mainStorageProofSizeSoftLimit :=
      ((field j "witness_config").toOption.bind (fun w => (nat w "main_storage_proof_size_soft_limit").toOption)).getD
        (2 ^ 32 - 1)
    extCompute := computeExt
    actionExecutionCompute := computeExecution
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
      ethImplicitGlobalContract := ((field wasm "eth_implicit_global_contract").toOption.bind (·.getBool?.toOption)).getD false
      bls12381NotInGroupFix :=
        ((field wasm "bls12381_not_in_group_fix").toOption.bind (·.getBool?.toOption)).getD false
      globalContractHostFns := hostFns
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
