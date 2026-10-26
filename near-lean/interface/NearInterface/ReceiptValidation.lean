import NearInterface.Boundary

/-!
# Validation of the receipts a call creates

After a successful function call the runtime validates every receipt the call
created (nearcore's `validate_receipt` for a new receipt) and, at the first
invalid one, fails the call with no effects
(`ActionErrorKind::NewReceiptValidationError`). The messages below are
nearcore's `Display` texts: the runtime reports them at the boundary
(`Near.Boundary.runtimeFailure`), and a contract model predicts them for its
own receipts with `callReceiptsError`.
-/

namespace NearInterface.ReceiptValidation

open Wasm Wasm.Near

/-! ## Messages -/

/-- `ActionErrorKind::NewReceiptValidationError`. -/
def newReceiptInvalid (detail : String) : String :=
  s!"An new action receipt created during a FunctionCall is not valid: {detail}"

def receiptSizeExceeded (size limit : Nat) : String :=
  s!"The size of the receipt exceeded the limit: {size} > {limit}"

def totalPrepaidGasExceeded (total limit : Nat) : String :=
  s!"The total prepaid gas {total} exceeds the limit {limit}"

def totalNumberOfActionsExceeded (count limit : Nat) : String :=
  s!"The total number of actions {count} exceeds the limit {limit}"

def integerOverflow : String := "Integer overflow during a compute"

def methodNameLengthExceeded (length limit : Nat) : String :=
  s!"The length of the method name {length} exceeds the maximum allowed length {limit} in a FunctionCall action"

def argumentsLengthExceeded (length limit : Nat) : String :=
  s!"The length of the arguments {length} exceeds the maximum allowed length {limit} in a FunctionCall action"

def zeroAttachedGas : String :=
  "The attached amount of gas in a FunctionCall action has to be a positive number"

/-! ## Receipts of function calls and transfers -/

/-- Receivers of the data receipt `k` produces: one for each dependency of a
later receipt of the same call on it. -/
def outputs (receipts : List RawReceipt) (k : Nat) : List Bytes :=
  receipts.flatMap fun r => (r.dependencies.filter (· == k)).map fun _ => r.receiverId

/-- Borsh size of a function call or transfer action; `none` for other actions. -/
def actionSize : PromiseAction → Option Nat
  | .functionCall method args _ _ => some (1 + 4 + method.length + 4 + args.length + 8 + 16)
  | .transfer _ => some (1 + 16)
  | _ => none

/-- Borsh size of the action receipt a promise becomes: header, signer, gas
price, output data receivers, input data ids and actions (`Receipt.newBorshSize`). -/
def receiptSize (predecessor signer : AccountId) (signerPk : Bytes) (outs : List Bytes)
    (r : RawReceipt) (actionsSize : Nat) : Nat :=
  4 + predecessor.bytes.length + 4 + r.receiverId.length + 32 + 1 + 4 + signer.bytes.length + 1 +
    signerPk.length + 16 + 4 + (outs.map fun o => 32 + 4 + o.length).sum +
    4 + 32 * (r.dependencies.length + if r.yieldDataId.isSome then 1 else 0) + 4 + actionsSize

/-- `validate_action` for a function call or transfer. -/
def actionError (limits : LimitConfig) : PromiseAction → Option String
  | .functionCall method args _ gas =>
    if gas.toNat == 0 then some zeroAttachedGas
    else if method.length > limits.maxLengthMethodName then
      some (methodNameLengthExceeded method.length limits.maxLengthMethodName)
    else if args.length > limits.maxArgumentsLength then
      some (argumentsLengthExceeded args.length limits.maxArgumentsLength)
    else none
  | _ => none

def attachedGas : PromiseAction → Nat
  | .functionCall _ _ _ gas => gas.toNat
  | _ => 0

/-- `validate_receipt` for one receipt `r` at index `k`, all of whose actions
are function calls and transfers: its size, then `validate_actions` (number
of actions, each action, total prepaid gas). -/
def receiptError (cfg : RuntimeConfig) (predecessor signer : AccountId) (signerPk : Bytes)
    (receipts : List RawReceipt) (r : RawReceipt) (k : Nat) : Option String :=
  let limits := cfg.wasm.limits
  match r.actions.mapM actionSize with
  | none => none
  | some sizes =>
    let size := receiptSize predecessor signer signerPk (outputs receipts k) r sizes.sum
    if size > limits.maxReceiptSize then
      some (newReceiptInvalid (receiptSizeExceeded size limits.maxReceiptSize))
    else if r.actions.length > limits.maxActionsPerReceipt then
      some (newReceiptInvalid (totalNumberOfActionsExceeded r.actions.length limits.maxActionsPerReceipt))
    else match r.actions.findSome? (actionError limits) with
      | some e => some (newReceiptInvalid e)
      | none =>
        let prepaid := (r.actions.map attachedGas).sum
        if prepaid ≥ 2 ^ 64 then some (newReceiptInvalid integerOverflow)
        else if prepaid > limits.maxTotalPrepaidGas then
          some (newReceiptInvalid (totalPrepaidGasExceeded prepaid limits.maxTotalPrepaidGas))
        else none

/-- The message of the first receipt the runtime rejects among those a call
created, for receipts of function calls and transfers (a receipt with another
kind of action is not checked here). `predecessor` is the calling contract. -/
def callReceiptsError (cfg : RuntimeConfig) (predecessor signer : AccountId) (signerPk : Bytes)
    (receipts : List RawReceipt) : Option String :=
  receipts.zipIdx.findSome? fun (r, k) => receiptError cfg predecessor signer signerPk receipts r k

end NearInterface.ReceiptValidation
