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
  /-- A gas key with full access: `GasKeyInfo { balance, num_nonces }`. Its nonces live in
  separate rows (`ChainState.gasKeyNonces`). -/
  | gasKeyFullAccess (balance numNonces : Nat)
  /-- A gas key restricted to function calls (`GasKeyFunctionCall`). -/
  | gasKeyFunctionCall (balance numNonces : Nat) (allowance : Option Nat) (receiverId : AccountId)
      (methodNames : List String)
  deriving BEq, Repr, Inhabited

/-- The balance and number of nonce lanes of a gas key, `none` for an ordinary key. -/
def AccessKeyPermission.gasKeyInfo? : AccessKeyPermission → Option (Nat × Nat)
  | .gasKeyFullAccess balance nonces | .gasKeyFunctionCall balance nonces .. => some (balance, nonces)
  | _ => none

structure AccessKey where
  nonce : Nat
  permission : AccessKeyPermission
  deriving BEq, Repr, Inhabited

deriving instance Repr for Wasm.GlobalContractId

/-- How a global contract is identified when deployed (`GlobalContractDeployMode`). -/
abbrev GlobalDeployMode := Wasm.GlobalContractDeployMode

inductive Action
  | createAccount
  | deployContract (code : ContractCode)
  | functionCall (methodName : String) (args : Bytes) (gas : Nat) (deposit : Nat)
  | transfer (deposit : Nat)
  | stake (stake : Nat) (publicKey : PublicKey)
  | addKey (publicKey : PublicKey) (accessKey : AccessKey)
  | deleteKey (publicKey : PublicKey)
  | deleteAccount (beneficiaryId : AccountId)
  /-- Use a global contract: the account's code becomes the registered global one. -/
  | useGlobalContract (contract : Wasm.GlobalContractId)
  /-- Publish `code` to every shard under its hash or the deploying account. -/
  | deployGlobalContract (code : ContractCode) (mode : GlobalDeployMode)
  /-- Fund the gas key `publicKey` of the receiver. -/
  | transferToGasKey (publicKey : PublicKey) (deposit : Nat)
  /-- Move `amount` from the receiver's gas key to its balance. -/
  | withdrawFromGasKey (publicKey : PublicKey) (amount : Nat)
  /-- A meta transaction (`Delegate`, or `DelegateV2` when `v2`): `actions` run at `receiverId` on
  behalf of `senderId`. `nonceIndex` selects a gas-key nonce lane. The signature is carried as given
  and checked by the runtime's injected verifier. -/
  | delegate (senderId receiverId : AccountId) (actions : List Action) (nonce : Nat)
      (nonceIndex : Option Nat) (maxBlockHeight : Nat) (publicKey : PublicKey) (signature : Bytes)
      (v2 : Bool)
  deriving Inhabited

mutual
/-- Tokens attached to an action; a delegate action carries the deposits of its inner actions. -/
def Action.deposit : Action → Nat
  | .functionCall _ _ _ d => d
  | .transfer d => d
  | .transferToGasKey _ d => d
  | .delegate _ _ actions .. => Action.depositList actions
  | _ => 0

def Action.depositList : List Action → Nat
  | [] => 0
  | a :: rest => a.deposit + Action.depositList rest
end

mutual
/-- Prepaid gas of an action; a delegate action carries the gas of its inner actions. -/
def Action.attachedGas : Action → Nat
  | .functionCall _ _ g _ => g
  | .delegate _ _ actions .. => Action.attachedGasList actions
  | _ => 0

def Action.attachedGasList : List Action → Nat
  | [] => 0
  | a :: rest => a.attachedGas + Action.attachedGasList rest
end

def Action.isDelegate : Action → Bool
  | .delegate .. => true
  | _ => false

def Action.isFunctionCall : Action → Bool
  | .functionCall .. => true
  | _ => false

structure Account where
  amount : Nat
  locked : Nat := 0
  code : Option ContractCode := none
  storageUsage : Nat
  /-- The global contract the account uses (`AccountContract::Global`/`GlobalByAccount`). -/
  global : Option Wasm.GlobalContractId := none
  /-- Serialized as `AccountV2`: set once an account uses a global contract and kept afterwards. -/
  versionTwo : Bool := false
  deriving Inhabited

/-- Whether the account carries a contract of any kind. -/
def Account.hasContract (a : Account) : Bool := a.code.isSome || a.global.isSome

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
  /-- A `PromiseYield` receipt: it waits for the data with this native id, which its
  creator handed to the contract. Such a receipt has no logical input data id. -/
  yieldDataId : Option Bytes := none
  deriving Inhabited

structure DataReceipt where
  dataId : DataId
  /-- `none` when the producing receipt failed. -/
  data : Option Bytes
  /-- A `PromiseResume` receipt: it resumes the yield with this native data id
  (and then `dataId` is unused). `data = none` is a timeout. -/
  resumeDataId : Option Bytes := none
  deriving BEq, Repr, Inhabited

/-- `GlobalContractDistributionReceipt` (V2): code to register under `id` on every shard. -/
structure GlobalDistribution where
  id : Wasm.GlobalContractId
  targetShard : Nat
  alreadyDelivered : List Nat := []
  code : ContractCode
  nonce : Nat
  deriving Inhabited

inductive ReceiptEnum
  | action (r : ActionReceipt)
  | data (d : DataReceipt)
  | globalDistribution (d : GlobalDistribution)
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

/-- The system actor is the predecessor of refunds and the receiver of distributions. -/
def systemReceiver : AccountId := systemAccount

def Receipt.isRefund (r : Receipt) : Bool := r.predecessorId == systemAccount

/-- A system transfer refunds a key's gas allowance when its signer is its receiver.
This is the pinned runtime's marker; balance refunds normally name `system`. -/
def Receipt.isGasRefund (r : Receipt) : Bool :=
  r.isRefund && match r.receipt with
    | .action a => a.signerId == r.receiverId
    | .data _ | .globalDistribution _ => false

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
  | delegateActionMustBeOnlyOne
  | gasKeyFunctionCallAllowanceNotAllowed
  | gasKeyInvalidNumNonces (requested limit : Nat)
  | addGasKeyWithNonZeroBalance (balance : Nat)
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
  /-- `UseGlobalContract` of an identifier no `DeployGlobalContract` has registered. -/
  | globalContractDoesNotExist (identifier : Wasm.GlobalContractId)
  | gasKeyDoesNotExist (id : AccountId) (publicKey : PublicKey)
  | insufficientGasKeyBalance (id : AccountId) (publicKey : PublicKey) (balance required : Nat)
  | gasKeyBalanceTooHigh (id : AccountId) (publicKey : Option PublicKey) (balance : Nat)
  | delegateActionInvalidSignature
  | delegateActionSenderDoesNotMatchTxReceiver (sender receiver : AccountId)
  | delegateActionExpired
  | delegateActionInvalidNonce (delegateNonce akNonce : Nat)
  | delegateActionNonceTooLarge (delegateNonce upperBound : Nat)
  | delegateActionInvalidNonceIndex (nonceIndex numNonces : Nat)
  /-- The delegate's key is unusable: `reason` names the `InvalidAccessKeyError`. -/
  | delegateActionAccessKeyError (reason : String)
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
