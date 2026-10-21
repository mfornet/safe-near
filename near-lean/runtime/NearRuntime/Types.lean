import NearVM

/-!
# Runtime types

Accounts, access keys, actions, receipts, transactions and execution
outcomes, mirroring `near_primitives`. Logical IDs are counters handed out
by the state; execution identity context can bind their native hashes.
Transaction signatures are trusted to be correct; consensus and cryptography are
outside the model (`notes/design/NEAR_RUNTIME.md`).
-/

namespace Near

open Wasm

abbrev AccountId := String
abbrev Bytes := List UInt8
abbrev PublicKey := Bytes
abbrev ReceiptId := Nat
abbrev DataId := Nat

/-- The account that sends refunds. -/
def systemAccount : AccountId := "system"

/-- Deployed contract code: the decoded module plus the size and a name for
its bytes (nearcore's code hash). Binary decoding is not available in Lean
yet, so code enters the model already decoded from WAT. -/
structure ContractCode where
  module : Module
  size : Nat
  hash : String
  /-- The external decoder could not supply this code. Replay adapters must
  report that limitation rather than substituting an executable empty module. -/
  decodeIssue : Option Wasm.Near.ExecutionIssue := none

instance : Inhabited ContractCode := ⟨{ module := default, size := 0, hash := "" }⟩

/-- The decoder remains trusted for module/hash correspondence. Byte size is
known from the supplied bytes and must not be delegated to decoder metadata. -/
def ContractCode.decodeSized (decoder : Bytes → ContractCode) (bytes : Bytes) : ContractCode :=
  { decoder bytes with size := bytes.length }

@[simp] theorem ContractCode.decodeSized_size (decoder : Bytes → ContractCode) (bytes : Bytes) :
    (ContractCode.decodeSized decoder bytes).size = bytes.length := rfl

theorem ContractCode.decodeSized_module (decoder : Bytes → ContractCode) (bytes : Bytes) :
    (ContractCode.decodeSized decoder bytes).module = (decoder bytes).module := rfl

inductive AccessKeyPermission
  | fullAccess
  /-- `allowance = none` means unlimited. `methodNames = []` allows every method. -/
  | functionCall (allowance : Option Nat) (receiverId : AccountId) (methodNames : List String)
  deriving BEq, Repr, Inhabited

structure AccessKey where
  nonce : Nat
  permission : AccessKeyPermission
  deriving BEq, Repr, Inhabited

inductive Action
  | createAccount
  | deployContract (code : ContractCode)
  | functionCall (methodName : String) (args : Bytes) (gas : Nat) (deposit : Nat)
  | transfer (deposit : Nat)
  | stake (stake : Nat) (publicKey : PublicKey)
  | addKey (publicKey : PublicKey) (accessKey : AccessKey)
  | deleteKey (publicKey : PublicKey)
  | deleteAccount (beneficiaryId : AccountId)
  deriving Inhabited

def Action.deposit : Action → Nat
  | .functionCall _ _ _ d => d
  | .transfer d => d
  | _ => 0

def Action.attachedGas : Action → Nat
  | .functionCall _ _ g _ => g
  | _ => 0

def Action.isFunctionCall : Action → Bool
  | .functionCall .. => true
  | _ => false

structure Account where
  amount : Nat
  locked : Nat := 0
  code : Option ContractCode := none
  storageUsage : Nat
  deriving Inhabited

structure DataReceiver where
  dataId : DataId
  receiverId : AccountId
  deriving BEq, Repr, Inhabited

structure ActionReceipt where
  signerId : AccountId
  signerPublicKey : PublicKey
  gasPrice : Nat
  outputDataReceivers : List DataReceiver := []
  inputDataIds : List DataId := []
  actions : List Action
  deriving Inhabited

structure DataReceipt where
  dataId : DataId
  /-- `none` when the producing receipt failed. -/
  data : Option Bytes
  deriving BEq, Repr, Inhabited

inductive ReceiptEnum
  | action (r : ActionReceipt)
  | data (d : DataReceipt)
  deriving Inhabited

structure Receipt where
  predecessorId : AccountId
  receiverId : AccountId
  receiptId : ReceiptId
  receipt : ReceiptEnum
  deriving Inhabited

def Receipt.actions : Receipt → List Action
  | { receipt := .action r, .. } => r.actions
  | _ => []

def Receipt.isRefund (r : Receipt) : Bool := r.predecessorId == systemAccount

/-- A system transfer refunds a key's gas allowance when its signer is its receiver.
This is the pinned runtime's marker; balance refunds normally name `system`. -/
def Receipt.isGasRefund (r : Receipt) : Bool :=
  r.isRefund && match r.receipt with
    | .action a => a.signerId == r.receiverId
    | .data _ => false

/-- Legacy transactions are monotonic; v1 can request strict sequential nonces. -/
inductive NonceMode where
  | monotonic
  | strict
  deriving Repr, BEq, DecidableEq, Inhabited

instance : LawfulBEq NonceMode where
  rfl := by intro mode; cases mode <;> rfl
  eq_of_beq := by intro a b h; cases a <;> cases b <;> cases h <;> rfl

/-- A transaction; the signature is trusted. -/
structure Transaction where
  /-- Native transaction envelope tag. V1 is enabled by the GasKeys feature. -/
  version : Nat := 0
  signerId : AccountId
  publicKey : PublicKey
  nonce : Nat
  nonceMode : NonceMode := .monotonic
  receiverId : AccountId
  actions : List Action
  deriving Inhabited

/-- Stateless action errors, before signer/key admission or transaction charges. -/
inductive ActionsValidationError
  | deleteActionMustBeFinal
  | totalPrepaidGasExceeded (total limit : Nat)
  | totalNumberOfActionsExceeded (count limit : Nat)
  | totalNumberOfDeployActionsExceeded (count limit : Nat)
  | addKeyMethodNamesNumberOfBytesExceeded (total limit : Nat)
  | addKeyMethodNameLengthExceeded (length limit : Nat)
  | integerOverflow
  | invalidAccountId (id : String)
  | contractSizeExceeded (size limit : Nat)
  | functionCallMethodNameLengthExceeded (length limit : Nat)
  | functionCallArgumentsLengthExceeded (length limit : Nat)
  | functionCallZeroAttachedGas
  | unsuitableStakingKey (key : PublicKey)
  deriving Repr, BEq, Inhabited

/-- Receipt and transaction failures, preserving stateless action error categories. -/
inductive RuntimeError
  | actionsValidation (error : ActionsValidationError)
  | accountAlreadyExists (id : AccountId)
  | accountDoesNotExist (id : AccountId)
  | createAccountNotAllowed (id predecessor : AccountId)
  | createAccountOnlyByRegistrar (id registrar predecessor : AccountId)
  | actorNoPermission (id actor : AccountId)
  | deleteKeyDoesNotExist (id : AccountId) (publicKey : PublicKey)
  | addKeyAlreadyExists (id : AccountId) (publicKey : PublicKey)
  | deleteAccountStaking (id : AccountId)
  | lackBalanceForState (id : AccountId) (amount : Nat)
  | triesToUnstake (id : AccountId)
  | triesToStake (id : AccountId) (stake locked balance : Nat)
  | insufficientStake (id : AccountId)
  | functionCallError (e : Wasm.Near.FunctionCallError)
  | deleteActionMustBeFinal
  | onlyImplicitAccountCreationAllowed (id : AccountId)
  | deleteAccountWithLargeState (id : AccountId)
  | invalidSigner (id : AccountId)
  | invalidTransactionVersion
  | transactionSizeExceeded (size limit : Nat)
  | invalidNonce (txNonce akNonce : Nat)
  | nonceTooLarge (txNonce upperBound : Nat)
  | invalidAccessKey (msg : String)
  | accessKeyNotFound (id : AccountId) (publicKey : PublicKey)
  | receiverMismatch (txReceiver keyReceiver : AccountId)
  | methodNameMismatch (methodName : String)
  | notEnoughAllowance (id : AccountId) (publicKey : PublicKey) (allowance cost : Nat)
  | notEnoughBalance (id : AccountId) (balance cost : Nat)
  | invalidReceiver (id : AccountId)
  | contractSizeExceeded (size limit : Nat)
  | tooManyActions (count limit : Nat)
  | executionIssue (issue : Wasm.Near.ExecutionIssue)
  deriving Repr, BEq, Inhabited

def RuntimeError.message : RuntimeError → String
  | .functionCallError e => e.message
  | e => s!"{repr e}"

/-- Runtime model limitations are not receipt failures on the reference chain. -/
def RuntimeError.issue? : RuntimeError → Option Wasm.Near.ExecutionIssue
  | .executionIssue issue => some issue
  | .functionCallError error => error.issue?
  | _ => none

inductive ExecutionStatus
  | failure (e : RuntimeError)
  | successValue (value : Bytes)
  | successReceiptId (id : ReceiptId)
  deriving Repr, BEq, Inhabited

def ExecutionStatus.isSuccess : ExecutionStatus → Bool
  | .failure _ => false
  | _ => true

structure ExecutionOutcome where
  /-- Failed receipt action, absent for transaction errors and final storage checks. -/
  failureIndex : Option Nat := none
  executorId : AccountId
  status : ExecutionStatus
  logs : List String := []
  receiptIds : List ReceiptId := []
  gasBurnt : Nat := 0
  tokensBurnt : Nat := 0
  deriving Inhabited

end Near
