import NearRuntime.Fees

namespace Near

open Wasm.Near

/-- Native diagnostic truncation takes at most 128 UTF-8 bytes without splitting a character. -/
def accountErrorPrefix : List Char → Nat → List Char
  | [], _ => []
  | char :: rest, budget =>
    let bytes := (String.singleton char).utf8ByteSize
    if bytes ≤ budget then char :: accountErrorPrefix rest (budget - bytes) else []

def validateActionPermission (limits : LimitConfig) : AccessKeyPermission → Except ActionsValidationError Unit
  | .fullAccess => pure ()
  | .functionCall _ receiver methods => do
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

/-- The modeled action transport trusts public-key decoding/curve validity externally.
Staking execution remains an explicit epoch-machinery limitation. -/
def validateAction (limits : LimitConfig) : Action → Except ActionsValidationError Unit
  | .functionCall method args gas _ => do
    if gas == 0 then throw .functionCallZeroAttachedGas
    if method.utf8ByteSize > limits.maxLengthMethodName then
      throw (.functionCallMethodNameLengthExceeded method.utf8ByteSize limits.maxLengthMethodName)
    if args.length > limits.maxArgumentsLength then
      throw (.functionCallArgumentsLengthExceeded args.length limits.maxArgumentsLength)
  | .deployContract code => do
    if code.size > limits.maxContractSize then
      throw (.contractSizeExceeded code.size limits.maxContractSize)
  | .addKey _ key => validateActionPermission limits key.permission
  | .deleteAccount beneficiary => do
    if !validAccountIdBytes beneficiary.toUTF8.toList then throw (.invalidAccountId beneficiary)
  | _ => pure ()

def validateActionOrder (limits : LimitConfig) : List Action → Except ActionsValidationError Unit
  | [] => pure ()
  | action :: rest => do
    if let .deleteAccount _ := action then
      if !rest.isEmpty then throw .deleteActionMustBeFinal
    validateAction limits action
    validateActionOrder limits rest

/-- Native `validate_actions` order for the modeled ordinary-key action kinds.
Counts precede ordered per-action checks; gas overflow/total limits follow them. -/
def validateTransactionActions (cfg : RuntimeConfig) (actions : List Action) :
    Except ActionsValidationError Unit := do
  let limits := cfg.wasm.limits
  if actions.length > limits.maxActionsPerReceipt then
    throw (.totalNumberOfActionsExceeded actions.length limits.maxActionsPerReceipt)
  let deploys := (actions.filter fun action => match action with | .deployContract _ => true | _ => false).length
  if deploys > limits.maxDeployActionsPerReceipt then
    throw (.totalNumberOfDeployActionsExceeded deploys limits.maxDeployActionsPerReceipt)
  validateActionOrder limits actions
  let prepaid := Fees.totalPrepaid actions
  if prepaid ≥ 2 ^ 64 then throw .integerOverflow
  if prepaid > limits.maxTotalPrepaidGas then
    throw (.totalPrepaidGasExceeded prepaid limits.maxTotalPrepaidGas)

end Near
