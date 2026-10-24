import NearNode.Primitives.Action

/-!
# Execution errors

`near-primitives::errors` at `=0.37.4`: the Borsh-encoded error trees reachable
from `ExecutionStatus::Failure`, namely `TxExecutionError`, `ActionError`,
`InvalidTxError` and everything below them. Enum tags are the explicit
discriminants of the Rust definitions.
-/

namespace Near.Node

open Borsh

/-- `MissingTrieValueContext`. -/
inductive MissingTrieValueContext where
  | trieIterator
  | triePrefetchingStorage
  | trieMemoryPartialStorage
  | trieStorage
  deriving BEq, Inhabited

instance : Codec MissingTrieValueContext :=
  .enum "MissingTrieValueContext"
    [.const 0 .trieIterator, .const 1 .triePrefetchingStorage, .const 2 .trieMemoryPartialStorage,
      .const 3 .trieStorage]

/-- `MissingTrieValue`. -/
structure MissingTrieValue where
  context : MissingTrieValueContext
  hash : CryptoHash
  deriving BEq, Inhabited

instance : Codec MissingTrieValue :=
  .iso (MissingTrieValueContext × CryptoHash) (fun (c, h) => ⟨c, h⟩) fun x => (x.context, x.hash)

/-- `StorageError`. -/
inductive StorageError where
  | storageInternalError
  | missingTrieValue (v : MissingTrieValue)
  | unexpectedTrieValue
  | storageInconsistentState (msg : String)
  | flatStorageBlockNotSupported (msg : String)
  | memTrieLoadingError (msg : String)
  deriving BEq, Inhabited

instance : Codec StorageError :=
  .enum "StorageError"
    [.const 0 .storageInternalError,
      .variant 1 MissingTrieValue .missingTrieValue fun
        | .missingTrieValue v => some v
        | _ => none,
      .const 2 .unexpectedTrieValue,
      .variant 3 String .storageInconsistentState fun
        | .storageInconsistentState m => some m
        | _ => none,
      .variant 4 String .flatStorageBlockNotSupported fun
        | .flatStorageBlockNotSupported m => some m
        | _ => none,
      .variant 5 String .memTrieLoadingError fun
        | .memTrieLoadingError m => some m
        | _ => none]

/-- `DepositCostFailureReason`. -/
inductive DepositCostFailureReason where
  | notEnoughBalance
  | lackBalanceForState
  deriving BEq, Inhabited

instance : Codec DepositCostFailureReason :=
  .enum "DepositCostFailureReason" [.const 0 .notEnoughBalance, .const 1 .lackBalanceForState]

/-- `PrepareError`. -/
inductive PrepareError where
  | serialization
  | deserialization
  | internalMemoryDeclared
  | gasInstrumentation
  | stackHeightInstrumentation
  | instantiate
  | memory
  | tooManyFunctions
  | tooManyLocals
  | tooManyTables
  | tooManyTableElements
  | functionBodyTooLarge
  | instrumentedCodeTooLarge
  | tooManyBlocksPerFunction
  | tooManyBlocksPerContract
  | tooManyTypes
  | tooManyParamsPerFunction
  | tooManyParamsPerContract
  | operandStackTooLarge
  deriving BEq, Inhabited

instance : Codec PrepareError :=
  .enum "PrepareError"
    [.const 0 .serialization, .const 1 .deserialization, .const 2 .internalMemoryDeclared,
      .const 3 .gasInstrumentation, .const 4 .stackHeightInstrumentation, .const 5 .instantiate,
      .const 6 .memory, .const 7 .tooManyFunctions, .const 8 .tooManyLocals,
      .const 9 .tooManyTables, .const 10 .tooManyTableElements, .const 11 .functionBodyTooLarge,
      .const 12 .instrumentedCodeTooLarge, .const 13 .tooManyBlocksPerFunction,
      .const 14 .tooManyBlocksPerContract, .const 15 .tooManyTypes,
      .const 16 .tooManyParamsPerFunction, .const 17 .tooManyParamsPerContract,
      .const 18 .operandStackTooLarge]

/-- `WasmTrap`. -/
inductive WasmTrap where
  | unreachable
  | incorrectCallIndirectSignature
  | memoryOutOfBounds
  | callIndirectOOB
  | illegalArithmetic
  | misalignedAtomicAccess
  | indirectCallToNull
  | stackOverflow
  | genericTrap
  deriving BEq, Inhabited

instance : Codec WasmTrap :=
  .enum "WasmTrap"
    [.const 0 .unreachable, .const 1 .incorrectCallIndirectSignature, .const 2 .memoryOutOfBounds,
      .const 3 .callIndirectOOB, .const 4 .illegalArithmetic, .const 5 .misalignedAtomicAccess,
      .const 6 .indirectCallToNull, .const 7 .stackOverflow, .const 8 .genericTrap]

/-- `MethodResolveError`. -/
inductive MethodResolveError where
  | methodEmptyName
  | methodNotFound
  | methodInvalidSignature
  deriving BEq, Inhabited

instance : Codec MethodResolveError :=
  .enum "MethodResolveError"
    [.const 0 .methodEmptyName, .const 1 .methodNotFound, .const 2 .methodInvalidSignature]

/-- `HostError`. -/
inductive HostError where
  | badUTF16
  | badUTF8
  | gasExceeded
  | gasLimitExceeded
  | balanceExceeded
  | emptyMethodName
  | guestPanic (panicMsg : String)
  | integerOverflow
  | invalidPromiseIndex (promiseIdx : UInt64)
  | cannotAppendActionToJointPromise
  | cannotReturnJointPromise
  | invalidPromiseResultIndex (resultIdx : UInt64)
  | invalidRegisterId (registerId : UInt64)
  | iteratorWasInvalidated (iteratorIndex : UInt64)
  | memoryAccessViolation
  | invalidReceiptIndex (receiptIndex : UInt64)
  | invalidIteratorIndex (iteratorIndex : UInt64)
  | invalidAccountId
  | invalidMethodName
  | invalidPublicKey
  | prohibitedInView (methodName : String)
  | numberOfLogsExceeded (limit : UInt64)
  | keyLengthExceeded (length limit : UInt64)
  | valueLengthExceeded (length limit : UInt64)
  | totalLogLengthExceeded (length limit : UInt64)
  | numberPromisesExceeded (numberOfPromises limit : UInt64)
  | numberInputDataDependenciesExceeded (numberOfInputDataDependencies limit : UInt64)
  | returnedValueLengthExceeded (length limit : UInt64)
  | contractSizeExceeded (size limit : UInt64)
  | deprecated (methodName : String)
  | ecRecoverError (msg : String)
  | altBn128InvalidInput (msg : String)
  | ed25519VerifyInvalidInput (msg : String)
  | p256VerifyInvalidInput (msg : String)
  deriving BEq, Inhabited

instance : Codec HostError :=
  .enum "HostError"
    [.const 0 .badUTF16, .const 1 .badUTF8, .const 2 .gasExceeded, .const 3 .gasLimitExceeded,
      .const 4 .balanceExceeded, .const 5 .emptyMethodName,
      .variant 6 String .guestPanic fun
        | .guestPanic m => some m
        | _ => none,
      .const 7 .integerOverflow,
      .variant 8 UInt64 .invalidPromiseIndex fun
        | .invalidPromiseIndex x => some x
        | _ => none,
      .const 9 .cannotAppendActionToJointPromise, .const 10 .cannotReturnJointPromise,
      .variant 11 UInt64 .invalidPromiseResultIndex fun
        | .invalidPromiseResultIndex x => some x
        | _ => none,
      .variant 12 UInt64 .invalidRegisterId fun
        | .invalidRegisterId x => some x
        | _ => none,
      .variant 13 UInt64 .iteratorWasInvalidated fun
        | .iteratorWasInvalidated x => some x
        | _ => none,
      .const 14 .memoryAccessViolation,
      .variant 15 UInt64 .invalidReceiptIndex fun
        | .invalidReceiptIndex x => some x
        | _ => none,
      .variant 16 UInt64 .invalidIteratorIndex fun
        | .invalidIteratorIndex x => some x
        | _ => none,
      .const 17 .invalidAccountId, .const 18 .invalidMethodName, .const 19 .invalidPublicKey,
      .variant 20 String .prohibitedInView fun
        | .prohibitedInView x => some x
        | _ => none,
      .variant 21 UInt64 .numberOfLogsExceeded fun
        | .numberOfLogsExceeded x => some x
        | _ => none,
      .variant 22 (UInt64 × UInt64) (fun (a, b) => .keyLengthExceeded a b) fun
        | .keyLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 23 (UInt64 × UInt64) (fun (a, b) => .valueLengthExceeded a b) fun
        | .valueLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 24 (UInt64 × UInt64) (fun (a, b) => .totalLogLengthExceeded a b) fun
        | .totalLogLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 25 (UInt64 × UInt64) (fun (a, b) => .numberPromisesExceeded a b) fun
        | .numberPromisesExceeded a b => some (a, b)
        | _ => none,
      .variant 26 (UInt64 × UInt64) (fun (a, b) => .numberInputDataDependenciesExceeded a b) fun
        | .numberInputDataDependenciesExceeded a b => some (a, b)
        | _ => none,
      .variant 27 (UInt64 × UInt64) (fun (a, b) => .returnedValueLengthExceeded a b) fun
        | .returnedValueLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 28 (UInt64 × UInt64) (fun (a, b) => .contractSizeExceeded a b) fun
        | .contractSizeExceeded a b => some (a, b)
        | _ => none,
      .variant 29 String .deprecated fun
        | .deprecated x => some x
        | _ => none,
      .variant 30 String .ecRecoverError fun
        | .ecRecoverError x => some x
        | _ => none,
      .variant 31 String .altBn128InvalidInput fun
        | .altBn128InvalidInput x => some x
        | _ => none,
      .variant 32 String .ed25519VerifyInvalidInput fun
        | .ed25519VerifyInvalidInput x => some x
        | _ => none,
      .variant 33 String .p256VerifyInvalidInput fun
        | .p256VerifyInvalidInput x => some x
        | _ => none]

/-- `CompilationError`. -/
inductive CompilationError where
  | codeDoesNotExist (accountId : AccountId)
  | prepareError (e : PrepareError)
  | wasmerCompileError (msg : String)
  deriving BEq, Inhabited

instance : Codec CompilationError :=
  .enum "CompilationError"
    [.variant 0 AccountId .codeDoesNotExist fun
        | .codeDoesNotExist a => some a
        | _ => none,
      .variant 1 PrepareError .prepareError fun
        | .prepareError e => some e
        | _ => none,
      .variant 2 String .wasmerCompileError fun
        | .wasmerCompileError m => some m
        | _ => none]

/-- `FunctionCallError`. Tag 6 is the retired `_EVMError`. -/
inductive FunctionCallError where
  | compilationError (e : CompilationError)
  | linkError (msg : String)
  | methodResolveError (e : MethodResolveError)
  | wasmTrap (e : WasmTrap)
  | wasmUnknownError
  | hostError (e : HostError)
  | evmError
  | executionError (msg : String)
  deriving BEq, Inhabited

instance : Codec FunctionCallError :=
  .enum "FunctionCallError"
    [.variant 0 CompilationError .compilationError fun
        | .compilationError e => some e
        | _ => none,
      .variant 1 String .linkError fun
        | .linkError m => some m
        | _ => none,
      .variant 2 MethodResolveError .methodResolveError fun
        | .methodResolveError e => some e
        | _ => none,
      .variant 3 WasmTrap .wasmTrap fun
        | .wasmTrap e => some e
        | _ => none,
      .const 4 .wasmUnknownError,
      .variant 5 HostError .hostError fun
        | .hostError e => some e
        | _ => none,
      .const 6 .evmError,
      .variant 7 String .executionError fun
        | .executionError m => some m
        | _ => none]

/-- `InvalidAccessKeyError`. -/
inductive InvalidAccessKeyError where
  | accessKeyNotFound (accountId : AccountId) (publicKey : PublicKey)
  | receiverMismatch (txReceiver : AccountId) (akReceiver : String)
  | methodNameMismatch (methodName : String)
  | requiresFullAccess
  | notEnoughAllowance (accountId : AccountId) (publicKey : PublicKey) (allowance cost : Balance)
  | depositWithFunctionCall
  | delegateActionRequiresNonGasKey
  | delegateActionRequiresGasKey
  deriving BEq, Inhabited

instance : Codec InvalidAccessKeyError :=
  .enum "InvalidAccessKeyError"
    [.variant 0 (AccountId × PublicKey) (fun (a, k) => .accessKeyNotFound a k) fun
        | .accessKeyNotFound a k => some (a, k)
        | _ => none,
      .variant 1 (AccountId × String) (fun (a, k) => .receiverMismatch a k) fun
        | .receiverMismatch a k => some (a, k)
        | _ => none,
      .variant 2 String .methodNameMismatch fun
        | .methodNameMismatch m => some m
        | _ => none,
      .const 3 .requiresFullAccess,
      .variant 4 (AccountId × PublicKey × Balance × Balance)
        (fun (a, k, l, c) => .notEnoughAllowance a k l c) fun
        | .notEnoughAllowance a k l c => some (a, k, l, c)
        | _ => none,
      .const 5 .depositWithFunctionCall, .const 6 .delegateActionRequiresNonGasKey,
      .const 7 .delegateActionRequiresGasKey]

/-- `ActionsValidationError`. -/
inductive ActionsValidationError where
  | deleteActionMustBeFinal
  | totalPrepaidGasExceeded (totalPrepaidGas limit : Gas)
  | totalNumberOfActionsExceeded (totalNumberOfActions limit : UInt64)
  | addKeyMethodNamesNumberOfBytesExceeded (totalNumberOfBytes limit : UInt64)
  | addKeyMethodNameLengthExceeded (length limit : UInt64)
  | integerOverflow
  | invalidAccountId (accountId : String)
  | contractSizeExceeded (size limit : UInt64)
  | functionCallMethodNameLengthExceeded (length limit : UInt64)
  | functionCallArgumentsLengthExceeded (length limit : UInt64)
  | unsuitableStakingKey (publicKey : PublicKey)
  | functionCallZeroAttachedGas
  | delegateActionMustBeOnlyOne
  | unsupportedProtocolFeature (protocolFeature : String) (version : ProtocolVersion)
  | invalidDeterministicStateInitReceiver (receiverId derivedId : AccountId)
  | deterministicStateInitKeyLengthExceeded (length limit : UInt64)
  | deterministicStateInitValueLengthExceeded (length limit : UInt64)
  | gasKeyInvalidNumNonces (requestedNonces limit : NonceIndex)
  | addGasKeyWithNonZeroBalance (balance : Balance)
  | gasKeyFunctionCallAllowanceNotAllowed
  | totalNumberOfDeployActionsExceeded (numberOfDeployActions limit : UInt64)
  deriving BEq, Inhabited

instance : Codec ActionsValidationError :=
  .enum "ActionsValidationError"
    [.const 0 .deleteActionMustBeFinal,
      .variant 1 (Gas × Gas) (fun (a, b) => .totalPrepaidGasExceeded a b) fun
        | .totalPrepaidGasExceeded a b => some (a, b)
        | _ => none,
      .variant 2 (UInt64 × UInt64) (fun (a, b) => .totalNumberOfActionsExceeded a b) fun
        | .totalNumberOfActionsExceeded a b => some (a, b)
        | _ => none,
      .variant 3 (UInt64 × UInt64) (fun (a, b) => .addKeyMethodNamesNumberOfBytesExceeded a b) fun
        | .addKeyMethodNamesNumberOfBytesExceeded a b => some (a, b)
        | _ => none,
      .variant 4 (UInt64 × UInt64) (fun (a, b) => .addKeyMethodNameLengthExceeded a b) fun
        | .addKeyMethodNameLengthExceeded a b => some (a, b)
        | _ => none,
      .const 5 .integerOverflow,
      .variant 6 String .invalidAccountId fun
        | .invalidAccountId a => some a
        | _ => none,
      .variant 7 (UInt64 × UInt64) (fun (a, b) => .contractSizeExceeded a b) fun
        | .contractSizeExceeded a b => some (a, b)
        | _ => none,
      .variant 8 (UInt64 × UInt64) (fun (a, b) => .functionCallMethodNameLengthExceeded a b) fun
        | .functionCallMethodNameLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 9 (UInt64 × UInt64) (fun (a, b) => .functionCallArgumentsLengthExceeded a b) fun
        | .functionCallArgumentsLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 10 PublicKey .unsuitableStakingKey fun
        | .unsuitableStakingKey k => some k
        | _ => none,
      .const 11 .functionCallZeroAttachedGas, .const 12 .delegateActionMustBeOnlyOne,
      .variant 13 (String × ProtocolVersion) (fun (f, v) => .unsupportedProtocolFeature f v) fun
        | .unsupportedProtocolFeature f v => some (f, v)
        | _ => none,
      .variant 14 (AccountId × AccountId) (fun (r, d) => .invalidDeterministicStateInitReceiver r d)
        fun
        | .invalidDeterministicStateInitReceiver r d => some (r, d)
        | _ => none,
      .variant 15 (UInt64 × UInt64) (fun (a, b) => .deterministicStateInitKeyLengthExceeded a b) fun
        | .deterministicStateInitKeyLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 16 (UInt64 × UInt64) (fun (a, b) => .deterministicStateInitValueLengthExceeded a b)
        fun
        | .deterministicStateInitValueLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 17 (NonceIndex × NonceIndex) (fun (a, b) => .gasKeyInvalidNumNonces a b) fun
        | .gasKeyInvalidNumNonces a b => some (a, b)
        | _ => none,
      .variant 18 Balance .addGasKeyWithNonZeroBalance fun
        | .addGasKeyWithNonZeroBalance b => some b
        | _ => none,
      .const 19 .gasKeyFunctionCallAllowanceNotAllowed,
      .variant 20 (UInt64 × UInt64) (fun (a, b) => .totalNumberOfDeployActionsExceeded a b) fun
        | .totalNumberOfDeployActionsExceeded a b => some (a, b)
        | _ => none]

/-- `ReceiptValidationError`. -/
inductive ReceiptValidationError where
  | invalidPredecessorId (accountId : String)
  | invalidReceiverId (accountId : String)
  | invalidSignerId (accountId : String)
  | invalidDataReceiverId (accountId : String)
  | returnedValueLengthExceeded (length limit : UInt64)
  | numberInputDataDependenciesExceeded (numberOfInputDataDependencies limit : UInt64)
  | actionsValidation (e : ActionsValidationError)
  | receiptSizeExceeded (size limit : UInt64)
  | invalidRefundTo (accountId : String)
  deriving BEq, Inhabited

instance : Codec ReceiptValidationError :=
  .enum "ReceiptValidationError"
    [.variant 0 String .invalidPredecessorId fun
        | .invalidPredecessorId a => some a
        | _ => none,
      .variant 1 String .invalidReceiverId fun
        | .invalidReceiverId a => some a
        | _ => none,
      .variant 2 String .invalidSignerId fun
        | .invalidSignerId a => some a
        | _ => none,
      .variant 3 String .invalidDataReceiverId fun
        | .invalidDataReceiverId a => some a
        | _ => none,
      .variant 4 (UInt64 × UInt64) (fun (a, b) => .returnedValueLengthExceeded a b) fun
        | .returnedValueLengthExceeded a b => some (a, b)
        | _ => none,
      .variant 5 (UInt64 × UInt64) (fun (a, b) => .numberInputDataDependenciesExceeded a b) fun
        | .numberInputDataDependenciesExceeded a b => some (a, b)
        | _ => none,
      .variant 6 ActionsValidationError .actionsValidation fun
        | .actionsValidation e => some e
        | _ => none,
      .variant 7 (UInt64 × UInt64) (fun (a, b) => .receiptSizeExceeded a b) fun
        | .receiptSizeExceeded a b => some (a, b)
        | _ => none,
      .variant 8 String .invalidRefundTo fun
        | .invalidRefundTo a => some a
        | _ => none]

/-- `NotNan<f64>` as its IEEE-754 bits. NaN is rejected, like Borsh does for floats. -/
structure NotNanF64 where
  bits : UInt64
  deriving BEq, Inhabited

instance : Codec NotNanF64 :=
  .tryIsoOf (α := UInt64) inferInstance
    (fun b =>
      if (b >>> 52) &&& 0x7FF == 0x7FF && b &&& 0xFFFFFFFFFFFFF != 0 then .error (.invalid "NaN")
      else .ok ⟨b⟩)
    (·.bits)

/-- `InvalidTxError`. -/
inductive InvalidTxError where
  | invalidAccessKeyError (e : InvalidAccessKeyError)
  | invalidSignerId (signerId : String)
  | signerDoesNotExist (signerId : AccountId)
  | invalidNonce (txNonce akNonce : Nonce)
  | nonceTooLarge (txNonce upperBound : Nonce)
  | invalidReceiverId (receiverId : String)
  | invalidSignature
  | notEnoughBalance (signerId : AccountId) (balance cost : Balance)
  | lackBalanceForState (signerId : AccountId) (amount : Balance)
  | costOverflow
  | invalidChain
  | expired
  | actionsValidation (e : ActionsValidationError)
  | transactionSizeExceeded (size limit : UInt64)
  | invalidTransactionVersion
  | storageError (e : StorageError)
  | shardCongested (shardId : UInt32) (congestionLevel : NotNanF64)
  | shardStuck (shardId : UInt32) (missedChunks : UInt64)
  | invalidNonceIndex (txNonceIndex : Option NonceIndex) (numNonces : NonceIndex)
  | notEnoughGasKeyBalance (signerId : AccountId) (balance cost : Balance)
  |
  notEnoughBalanceForDeposit (signerId : AccountId) (balance cost : Balance)
    (reason : DepositCostFailureReason)
  deriving BEq, Inhabited

instance : Codec InvalidTxError :=
  .enum "InvalidTxError"
    [.variant 0 InvalidAccessKeyError .invalidAccessKeyError fun
        | .invalidAccessKeyError e => some e
        | _ => none,
      .variant 1 String .invalidSignerId fun
        | .invalidSignerId s => some s
        | _ => none,
      .variant 2 AccountId .signerDoesNotExist fun
        | .signerDoesNotExist s => some s
        | _ => none,
      .variant 3 (Nonce × Nonce) (fun (a, b) => .invalidNonce a b) fun
        | .invalidNonce a b => some (a, b)
        | _ => none,
      .variant 4 (Nonce × Nonce) (fun (a, b) => .nonceTooLarge a b) fun
        | .nonceTooLarge a b => some (a, b)
        | _ => none,
      .variant 5 String .invalidReceiverId fun
        | .invalidReceiverId s => some s
        | _ => none,
      .const 6 .invalidSignature,
      .variant 7 (AccountId × Balance × Balance) (fun (s, b, c) => .notEnoughBalance s b c) fun
        | .notEnoughBalance s b c => some (s, b, c)
        | _ => none,
      .variant 8 (AccountId × Balance) (fun (s, a) => .lackBalanceForState s a) fun
        | .lackBalanceForState s a => some (s, a)
        | _ => none,
      .const 9 .costOverflow, .const 10 .invalidChain, .const 11 .expired,
      .variant 12 ActionsValidationError .actionsValidation fun
        | .actionsValidation e => some e
        | _ => none,
      .variant 13 (UInt64 × UInt64) (fun (a, b) => .transactionSizeExceeded a b) fun
        | .transactionSizeExceeded a b => some (a, b)
        | _ => none,
      .const 14 .invalidTransactionVersion,
      .variant 15 StorageError .storageError fun
        | .storageError e => some e
        | _ => none,
      .variant 16 (UInt32 × NotNanF64) (fun (s, l) => .shardCongested s l) fun
        | .shardCongested s l => some (s, l)
        | _ => none,
      .variant 17 (UInt32 × UInt64) (fun (s, m) => .shardStuck s m) fun
        | .shardStuck s m => some (s, m)
        | _ => none,
      .variant 18 (Option NonceIndex × NonceIndex) (fun (t, n) => .invalidNonceIndex t n) fun
        | .invalidNonceIndex t n => some (t, n)
        | _ => none,
      .variant 19 (AccountId × Balance × Balance) (fun (s, b, c) => .notEnoughGasKeyBalance s b c)
        fun
        | .notEnoughGasKeyBalance s b c => some (s, b, c)
        | _ => none,
      .variant 20 (AccountId × Balance × Balance × DepositCostFailureReason)
        (fun (s, b, c, r) => .notEnoughBalanceForDeposit s b c r) fun
        | .notEnoughBalanceForDeposit s b c r => some (s, b, c, r)
        | _ => none]

/-- `ActionErrorKind`. -/
inductive ActionErrorKind where
  | accountAlreadyExists (accountId : AccountId)
  | accountDoesNotExist (accountId : AccountId)
  | createAccountOnlyByRegistrar (accountId registrarAccountId predecessorId : AccountId)
  | createAccountNotAllowed (accountId predecessorId : AccountId)
  | actorNoPermission (accountId actorId : AccountId)
  | deleteKeyDoesNotExist (accountId : AccountId) (publicKey : PublicKey)
  | addKeyAlreadyExists (accountId : AccountId) (publicKey : PublicKey)
  | deleteAccountStaking (accountId : AccountId)
  | lackBalanceForState (accountId : AccountId) (amount : Balance)
  | triesToUnstake (accountId : AccountId)
  | triesToStake (accountId : AccountId) (stake locked balance : Balance)
  | insufficientStake (accountId : AccountId) (stake minimumStake : Balance)
  | functionCallError (e : FunctionCallError)
  | newReceiptValidationError (e : ReceiptValidationError)
  | onlyImplicitAccountCreationAllowed (accountId : AccountId)
  | deleteAccountWithLargeState (accountId : AccountId)
  | delegateActionInvalidSignature
  | delegateActionSenderDoesNotMatchTxReceiver (senderId receiverId : AccountId)
  | delegateActionExpired
  | delegateActionAccessKeyError (e : InvalidAccessKeyError)
  | delegateActionInvalidNonce (delegateNonce akNonce : Nonce)
  | delegateActionNonceTooLarge (delegateNonce upperBound : Nonce)
  | globalContractDoesNotExist (identifier : GlobalContractIdentifier)
  | gasKeyDoesNotExist (accountId : AccountId) (publicKey : PublicKey)
  |
  insufficientGasKeyBalance (accountId : AccountId) (publicKey : PublicKey)
    (balance required : Balance)
  | gasKeyBalanceTooHigh (accountId : AccountId) (publicKey : Option PublicKey) (balance : Balance)
  | delegateActionInvalidNonceIndex (nonceIndex numNonces : NonceIndex)
  deriving BEq, Inhabited

instance : Codec ActionErrorKind :=
  .enum "ActionErrorKind"
    [.variant 0 AccountId .accountAlreadyExists fun
        | .accountAlreadyExists a => some a
        | _ => none,
      .variant 1 AccountId .accountDoesNotExist fun
        | .accountDoesNotExist a => some a
        | _ => none,
      .variant 2 (AccountId × AccountId × AccountId)
        (fun (a, r, p) => .createAccountOnlyByRegistrar a r p) fun
        | .createAccountOnlyByRegistrar a r p => some (a, r, p)
        | _ => none,
      .variant 3 (AccountId × AccountId) (fun (a, p) => .createAccountNotAllowed a p) fun
        | .createAccountNotAllowed a p => some (a, p)
        | _ => none,
      .variant 4 (AccountId × AccountId) (fun (a, p) => .actorNoPermission a p) fun
        | .actorNoPermission a p => some (a, p)
        | _ => none,
      .variant 5 (AccountId × PublicKey) (fun (a, k) => .deleteKeyDoesNotExist a k) fun
        | .deleteKeyDoesNotExist a k => some (a, k)
        | _ => none,
      .variant 6 (AccountId × PublicKey) (fun (a, k) => .addKeyAlreadyExists a k) fun
        | .addKeyAlreadyExists a k => some (a, k)
        | _ => none,
      .variant 7 AccountId .deleteAccountStaking fun
        | .deleteAccountStaking a => some a
        | _ => none,
      .variant 8 (AccountId × Balance) (fun (a, b) => .lackBalanceForState a b) fun
        | .lackBalanceForState a b => some (a, b)
        | _ => none,
      .variant 9 AccountId .triesToUnstake fun
        | .triesToUnstake a => some a
        | _ => none,
      .variant 10 (AccountId × Balance × Balance × Balance)
        (fun (a, s, l, b) => .triesToStake a s l b) fun
        | .triesToStake a s l b => some (a, s, l, b)
        | _ => none,
      .variant 11 (AccountId × Balance × Balance) (fun (a, s, m) => .insufficientStake a s m) fun
        | .insufficientStake a s m => some (a, s, m)
        | _ => none,
      .variant 12 FunctionCallError .functionCallError fun
        | .functionCallError e => some e
        | _ => none,
      .variant 13 ReceiptValidationError .newReceiptValidationError fun
        | .newReceiptValidationError e => some e
        | _ => none,
      .variant 14 AccountId .onlyImplicitAccountCreationAllowed fun
        | .onlyImplicitAccountCreationAllowed a => some a
        | _ => none,
      .variant 15 AccountId .deleteAccountWithLargeState fun
        | .deleteAccountWithLargeState a => some a
        | _ => none,
      .const 16 .delegateActionInvalidSignature,
      .variant 17 (AccountId × AccountId)
        (fun (s, r) => .delegateActionSenderDoesNotMatchTxReceiver s r) fun
        | .delegateActionSenderDoesNotMatchTxReceiver s r => some (s, r)
        | _ => none,
      .const 18 .delegateActionExpired,
      .variant 19 InvalidAccessKeyError .delegateActionAccessKeyError fun
        | .delegateActionAccessKeyError e => some e
        | _ => none,
      .variant 20 (Nonce × Nonce) (fun (a, b) => .delegateActionInvalidNonce a b) fun
        | .delegateActionInvalidNonce a b => some (a, b)
        | _ => none,
      .variant 21 (Nonce × Nonce) (fun (a, b) => .delegateActionNonceTooLarge a b) fun
        | .delegateActionNonceTooLarge a b => some (a, b)
        | _ => none,
      .variant 22 GlobalContractIdentifier .globalContractDoesNotExist fun
        | .globalContractDoesNotExist i => some i
        | _ => none,
      .variant 23 (AccountId × PublicKey) (fun (a, k) => .gasKeyDoesNotExist a k) fun
        | .gasKeyDoesNotExist a k => some (a, k)
        | _ => none,
      .variant 24 (AccountId × PublicKey × Balance × Balance)
        (fun (a, k, b, r) => .insufficientGasKeyBalance a k b r) fun
        | .insufficientGasKeyBalance a k b r => some (a, k, b, r)
        | _ => none,
      .variant 25 (AccountId × Option PublicKey × Balance)
        (fun (a, k, b) => .gasKeyBalanceTooHigh a k b) fun
        | .gasKeyBalanceTooHigh a k b => some (a, k, b)
        | _ => none,
      .variant 26 (NonceIndex × NonceIndex) (fun (a, b) => .delegateActionInvalidNonceIndex a b) fun
        | .delegateActionInvalidNonceIndex a b => some (a, b)
        | _ => none]

/-- `ActionError`. -/
structure ActionError where
  index : Option UInt64
  kind : ActionErrorKind
  deriving BEq, Inhabited

instance : Codec ActionError :=
  .iso (Option UInt64 × ActionErrorKind) (fun (i, k) => ⟨i, k⟩) fun x => (x.index, x.kind)

/-- `TxExecutionError`. -/
inductive TxExecutionError where
  | actionError (e : ActionError)
  | invalidTxError (e : InvalidTxError)
  deriving BEq, Inhabited

instance : Codec TxExecutionError :=
  .enum "TxExecutionError"
    [.variant 0 ActionError .actionError fun
        | .actionError e => some e
        | _ => none,
      .variant 1 InvalidTxError .invalidTxError fun
        | .invalidTxError e => some e
        | _ => none]

end Near.Node
