import NearRuntime.Fees
import NearRuntime.StakingKey

namespace Near

open Wasm.Near

/-- Native diagnostic truncation takes at most 128 UTF-8 bytes without splitting a character. -/
def accountErrorPrefix : List Char → Nat → List Char
  | [], _ => []
  | char :: rest, budget =>
    let bytes := (String.singleton char).utf8ByteSize
    if bytes ≤ budget then char :: accountErrorPrefix rest (budget - bytes) else []

def validateFunctionCallKey (limits : LimitConfig) (receiver : String) (methods : List String) :
    Except ActionsValidationError Unit := do
  if limits.accountIdValidityRulesVersion != 0 && !validAccountIdBytes receiver.toUTF8.toList then
    throw (.invalidAccountId (String.ofList (accountErrorPrefix receiver.toList 128)))
  let mut total := 0
  for method in methods do
    let length := method.utf8ByteSize
    if length > limits.maxLengthMethodName then
      throw (.addKeyMethodNameLengthExceeded length limits.maxLengthMethodName)
    total := total + length + 1
  if total > limits.maxNumberBytesMethodNames then
    throw (.addKeyMethodNamesNumberOfBytesExceeded total limits.maxNumberBytesMethodNames)

/-- `AccessKeyPermission::MAX_NONCES_FOR_GAS_KEY`. -/
def maxNoncesForGasKey : Nat := 1024

def validateActionPermission (limits : LimitConfig) : AccessKeyPermission → Except ActionsValidationError Unit
  | .fullAccess => pure ()
  | .functionCall _ receiver methods => validateFunctionCallKey limits receiver methods
  | .gasKeyFullAccess balance nonces => do
    if nonces == 0 || nonces > maxNoncesForGasKey then
      throw (.gasKeyInvalidNumNonces nonces maxNoncesForGasKey)
    if balance != 0 then throw (.addGasKeyWithNonZeroBalance balance)
  | .gasKeyFunctionCall balance nonces allowance receiver methods => do
    validateFunctionCallKey limits receiver methods
    if allowance.isSome then throw .gasKeyFunctionCallAllowanceNotAllowed
    if nonces == 0 || nonces > maxNoncesForGasKey then
      throw (.gasKeyInvalidNumNonces nonces maxNoncesForGasKey)
    if balance != 0 then throw (.addGasKeyWithNonZeroBalance balance)

/-- Whether an action counts against `max_deploy_actions_per_receipt`. -/
def Action.isDeploy : Action → Bool
  | .deployContract _ | .deployGlobalContract .. => true
  | _ => false

mutual
/-- Public keys use native decoded encodings. Staking eligibility is checked
mathematically; staking execution still requires unmodeled epoch machinery.
`validate_actions`: counts, deploys, then each action in order (a delegate action validates
the actions it carries the same way), then the prepaid gas. -/
def validateAction (limits : LimitConfig) (action : Action) : Except ActionsValidationError Unit :=
  match action with
  | .functionCall method args gas _ => do
    if gas == 0 then throw .functionCallZeroAttachedGas
    if method.utf8ByteSize > limits.maxLengthMethodName then
      throw (.functionCallMethodNameLengthExceeded method.utf8ByteSize limits.maxLengthMethodName)
    if args.length > limits.maxArgumentsLength then
      throw (.functionCallArgumentsLengthExceeded args.length limits.maxArgumentsLength)
  | .deployContract code => do
    if code.size > limits.maxContractSize then
      throw (.contractSizeExceeded code.size limits.maxContractSize)
  | .deployGlobalContract code _ => do
    if code.size > limits.maxContractSize then
      throw (.contractSizeExceeded code.size limits.maxContractSize)
  | .stake _ key => do
    unless StakingKey.suitable key do throw (.unsuitableStakingKey key)
  | .addKey _ key => validateActionPermission limits key.permission
  | .useGlobalContract (.accountId id) => do
    if !validAccountIdBytes id then throw (.invalidAccountId ((String.fromUTF8? ⟨id.toArray⟩).getD ""))
  | .deleteAccount beneficiary => do
    if !validAccountIdBytes beneficiary.toUTF8.toList then throw (.invalidAccountId beneficiary)
  | .delegate _ _ inner .. => validateActions limits inner
  | _ => pure ()
termination_by (sizeOf action, 0)

def validateActions (limits : LimitConfig) (actions : List Action) :
    Except ActionsValidationError Unit := do
  if actions.length > limits.maxActionsPerReceipt then
    throw (.totalNumberOfActionsExceeded actions.length limits.maxActionsPerReceipt)
  let deploys := (actions.filter Action.isDeploy).length
  if deploys > limits.maxDeployActionsPerReceipt then
    throw (.totalNumberOfDeployActionsExceeded deploys limits.maxDeployActionsPerReceipt)
  validateActionOrder limits false actions
  let prepaid := Fees.totalPrepaid actions
  if prepaid ≥ 2 ^ 64 then throw .integerOverflow
  if prepaid > limits.maxTotalPrepaidGas then
    throw (.totalPrepaidGasExceeded prepaid limits.maxTotalPrepaidGas)
termination_by (sizeOf actions, 1)

def validateActionOrder (limits : LimitConfig) (foundDelegate : Bool) (actions : List Action) :
    Except ActionsValidationError Unit :=
  match actions with
  | [] => pure ()
  | action :: rest => do
    let mut found := foundDelegate
    if let .deleteAccount _ := action then
      if !rest.isEmpty then throw .deleteActionMustBeFinal
    else if let .delegate .. := action then
      if found then throw .delegateActionMustBeOnlyOne
      found := true
    validateAction limits action
    validateActionOrder limits found rest
termination_by (sizeOf actions, 0)
end

/-- Native `validate_actions` for a transaction's actions. -/
def validateTransactionActions (cfg : RuntimeConfig) (actions : List Action) :
    Except ActionsValidationError Unit :=
  validateActions cfg.wasm.limits actions

end Near
