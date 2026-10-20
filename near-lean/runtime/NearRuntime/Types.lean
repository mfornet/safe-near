import NearVM

/-!
# Runtime types

Accounts, access keys, actions, receipts, transactions and execution
outcomes, mirroring `near_primitives`. Hashes and signatures are not
modelled: ids are counters handed out by the state, and transactions are
trusted to be correctly signed (the chain layer is the "trustless
manipulator" of `notes/design/NEAR_RUNTIME.md`).
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

instance : Inhabited ContractCode := ⟨{ module := default, size := 0, hash := "" }⟩

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

/-- A transaction; the signature is trusted. -/
structure Transaction where
  signerId : AccountId
  publicKey : PublicKey
  nonce : Nat
  nonceMode : NonceMode := .monotonic
  receiverId : AccountId
  actions : List Action
  deriving Inhabited

/-- Why a receipt or transaction failed (`ActionErrorKind` and
`InvalidTxError`, flattened). -/
inductive RuntimeError
  | accountAlreadyExists (id : AccountId)
  | accountDoesNotExist (id : AccountId)
  | createAccountNotAllowed (id predecessor : AccountId)
  | actorNoPermission (id actor : AccountId)
  | deleteKeyDoesNotExist (id : AccountId)
  | addKeyAlreadyExists (id : AccountId)
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
  | invalidNonce (txNonce akNonce : Nat)
  | nonceTooLarge (txNonce upperBound : Nat)
  | invalidAccessKey (msg : String)
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
  executorId : AccountId
  status : ExecutionStatus
  logs : List String := []
  receiptIds : List ReceiptId := []
  gasBurnt : Nat := 0
  tokensBurnt : Nat := 0
  deriving Inhabited

end Near
