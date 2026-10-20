import Model.State
import Model.Env

/-!
# Method calls, outcomes and panics

`Call` enumerates every exported method of the contract with typed
arguments (JSON decoding of arguments is the runtime's job). `Outcome` is
everything a successful execution produces; `Panic` enumerates every way an
execution can fail, each matching one panic in the Rust source.
-/

namespace WNear

/-- Every exported method of the contract, with decoded arguments. -/
@[blueprint "def:call"
  (statement := /-- One of the fifteen exported methods with its decoded arguments. -/)]
inductive Call
  /-- `new()` (`#[init]`). -/
  | new
  /-- `near_deposit()` (`#[payable]`). -/
  | nearDeposit
  /-- `near_withdraw(amount)` (`#[payable]`, 1 yoctoNEAR). -/
  | nearWithdraw (amount : Nat)
  /-- `ft_transfer(receiver_id, amount, memo)` (`#[payable]`, 1 yoctoNEAR). -/
  | ftTransfer (receiver : AccountId) (amount : Nat) (memo : Option String)
  /-- `ft_transfer_call(receiver_id, amount, memo, msg)` (`#[payable]`, 1 yoctoNEAR). -/
  | ftTransferCall (receiver : AccountId) (amount : Nat) (memo : Option String) (msg : String)
  /-- `ft_resolve_transfer(sender_id, receiver_id, amount)` (`#[private]` callback). -/
  | ftResolveTransfer (sender receiver : AccountId) (amount : Nat)
  /-- `ft_total_supply()` (view). -/
  | ftTotalSupply
  /-- `ft_balance_of(account_id)` (view). -/
  | ftBalanceOf (account : AccountId)
  /-- `ft_metadata()` (view). -/
  | ftMetadata
  /-- `storage_deposit(account_id, registration_only)` (`#[payable]`). -/
  | storageDeposit (account : Option AccountId) (registrationOnly : Option Bool)
  /-- `storage_withdraw(amount)` (`#[payable]`, 1 yoctoNEAR). -/
  | storageWithdraw (amount : Option Nat)
  /-- `storage_unregister(force)` (`#[payable]`, 1 yoctoNEAR). -/
  | storageUnregister (force : Option Bool)
  /-- `storage_balance_bounds()` (view). -/
  | storageBalanceBounds
  /-- `storage_balance_of(account_id)` (view). -/
  | storageBalanceOf (account : AccountId)
  /-- `storage_minimum_balance()` (view). -/
  | storageMinimumBalance
  deriving DecidableEq, Repr

namespace Call

/-- Numeric JSON arguments must fit the Rust `U128` wrapper. The mathematical
methods retain natural-number arithmetic; refinement applies to decodable calls. -/
def WF : Call → Prop
  | .nearWithdraw amount | .ftTransfer _ amount _ | .ftTransferCall _ amount _ _
  | .ftResolveTransfer _ _ amount => amount < u128Bound
  | .storageWithdraw (some amount) => amount < u128Bound
  | _ => True

instance (call : Call) : Decidable call.WF := by
  cases call <;> simp only [WF]
  all_goals first | infer_instance | (split <;> infer_instance)

def methodName : Call → String
  | new => "new"
  | nearDeposit => "near_deposit"
  | nearWithdraw _ => "near_withdraw"
  | ftTransfer .. => "ft_transfer"
  | ftTransferCall .. => "ft_transfer_call"
  | ftResolveTransfer .. => "ft_resolve_transfer"
  | ftTotalSupply => "ft_total_supply"
  | ftBalanceOf _ => "ft_balance_of"
  | ftMetadata => "ft_metadata"
  | storageDeposit .. => "storage_deposit"
  | storageWithdraw _ => "storage_withdraw"
  | storageUnregister _ => "storage_unregister"
  | storageBalanceBounds => "storage_balance_bounds"
  | storageBalanceOf _ => "storage_balance_of"
  | storageMinimumBalance => "storage_minimum_balance"

/-- `&self` methods: no deposit check, no state write-back. -/
def isView : Call → Bool
  | ftTotalSupply | ftBalanceOf _ | ftMetadata | storageBalanceBounds
  | storageBalanceOf _ | storageMinimumBalance => true
  | _ => false

/-- `#[payable]` methods: attached deposit accepted. -/
def isPayable : Call → Bool
  | nearDeposit | nearWithdraw _ | ftTransfer .. | ftTransferCall ..
  | storageDeposit .. | storageWithdraw _ | storageUnregister _ => true
  | _ => false

/-- `#[private]` methods: predecessor must be the contract itself. -/
def isPrivate : Call → Bool
  | ftResolveTransfer .. => true
  | _ => false

end Call

/-- Cross-contract calls the contract schedules. -/
inductive OutgoingCall
  /-- `ft_on_transfer(sender_id, amount, msg)` on the receiver. -/
  | ftOnTransfer (sender : AccountId) (amount : Nat) (msg : String)
  /-- `ft_resolve_transfer(sender_id, receiver_id, amount)` on itself. -/
  | ftResolveTransfer (sender receiver : AccountId) (amount : Nat)
  deriving DecidableEq, Repr

/-- Promises created by one execution. -/
@[blueprint "def:promise"
  (statement := /-- A promise created by an execution: a NEAR transfer, a function call with deposit and gas, or a promise followed by a callback. -/)]
inductive Promise
  /-- `Promise::new(receiver).transfer(amount)`. -/
  | transfer (receiver : AccountId) (amount : Nat)
  /-- A function call with attached deposit and gas. -/
  | call (receiver : AccountId) (method : OutgoingCall) (deposit : Nat) (gas : Nat)
  /-- `first.then(callback)`. -/
  | «then» (first : Promise) (callback : Promise)
  deriving DecidableEq, Repr

/-- yoctoNEAR leaving the contract when the promise is created. -/
def Promise.transferred : Promise → Nat
  | .transfer _ amount => amount
  | .call _ _ deposit _ => deposit
  | .then p q => p.transferred + q.transferred

structure StorageBalance where
  total : Nat
  available : Nat
  deriving DecidableEq, Repr

structure StorageBalanceBounds where
  min : Nat
  max : Option Nat
  deriving DecidableEq, Repr

structure Metadata where
  spec : String
  name : String
  symbol : String
  icon : Option String
  reference : Option String
  referenceHash : Option (List UInt8)
  decimals : Nat
  deriving DecidableEq, Repr

/-- Return values. -/
inductive Ret
  | unit
  | u128 (n : Nat)
  | bool (b : Bool)
  | storageBalance (b : StorageBalance)
  | optStorageBalance (b : Option StorageBalance)
  | storageBalanceBounds (b : StorageBalanceBounds)
  | metadata (m : Metadata)
  /-- Delegate the result to this receipt in creation order (flattening `then`
  chains from left to right). This is a local receipt index, not returned bytes
  and not a raw VM promise handle. -/
  | promise (receiptIndex : Nat)
  deriving DecidableEq, Repr

/-- Everything a successful execution produces. -/
@[blueprint "def:outcome"
  (statement := /-- The result of a successful execution: the new state, the promises created, the return value and the logs. -/)]
structure Outcome where
  state : State
  promises : List Promise := []
  ret : Ret := .unit
  logs : List String := []

/-- yoctoNEAR the execution sends out of the contract. -/
def Outcome.nearOut (o : Outcome) : Nat := (o.promises.map Promise.transferred).sum

/-- Every way an execution can fail. Each constructor is one panic site in the
Rust source (contract, near-contract-standards 3.1.0, or near-sdk 3.1.0). -/
@[blueprint "def:panic"
  (statement := /-- The ways an execution can fail; one constructor per panic site in the contract, in near-contract-standards 3.1.0 and in the near-sdk 3.1.0 wrapper. -/)]
inductive Panic
  /-- SDK wrapper: `Method {m} doesn't accept deposit`. -/
  | depositNotAccepted (method : String)
  /-- SDK wrapper: `Method {m} is private`. -/
  | privateMethod (method : String)
  /-- SDK `#[init]`: `The contract has already been initialized`. -/
  | alreadyInitialized
  /-- `PanicOnDefault`: `The contract is not initialized`. -/
  | notInitialized
  /-- `assert_one_yocto`: `Requires attached deposit of exactly 1 yoctoNEAR`. -/
  | requiresOneYocto
  /-- `near_deposit`: `Requires positive attached deposit`. -/
  | requiresPositiveDeposit
  /-- `near_deposit`: `ERR_DEPOSIT_TOO_SMALL`. -/
  | depositTooSmall
  /-- `internal_unwrap_balance_of` / `storage_withdraw`: `The account {a} is not registered`. -/
  | notRegistered (account : AccountId)
  /-- `internal_register_account`: `The account is already registered`. -/
  | alreadyRegistered
  /-- `internal_withdraw`: `The account doesn't have enough balance`. -/
  | notEnoughBalance
  /-- `internal_deposit`: `Nat overflow`. -/
  | balanceOverflow
  /-- `internal_deposit` / `internal_withdraw`: `Total supply overflow`. -/
  | totalSupplyOverflow
  /-- `internal_transfer`: `Sender and receiver should be different`. -/
  | sameSenderReceiver
  /-- `internal_transfer`: `The amount should be a positive number`. -/
  | amountNotPositive
  /-- `storage_deposit`: `The attached deposit is less than the mimimum storage balance` (sic). -/
  | storageDepositTooSmall
  /-- `storage_withdraw`: `The amount is greater than the available storage balance`. -/
  | storageWithdrawPositive
  /-- `storage_unregister`: `Can't unregister the account with the positive balance without force`. -/
  | unregisterWithBalance
  /-- `ft_resolve_transfer`: `promise_result(0)` requested outside a callback (host error). -/
  | noPromiseResult
  /-- `ft_resolve_transfer`: `PromiseResult::NotReady => unreachable!()`. -/
  | promiseNotReady
  /-- An unchecked integer operation overflowed (`overflow-checks = true` in the release profile). -/
  | arithmeticOverflow
  deriving DecidableEq, Repr

/-- Expected diagnostic fragment. Contract panics may have a runtime prefix
or source location; missing promise results are structured host errors. -/
def Panic.message : Panic → String
  | depositNotAccepted m => s!"Method {m} doesn't accept deposit"
  | privateMethod m => s!"Method {m} is private"
  | alreadyInitialized => "The contract has already been initialized"
  | notInitialized => "The contract is not initialized"
  | requiresOneYocto => "Requires attached deposit of exactly 1 yoctoNEAR"
  | requiresPositiveDeposit => "Requires positive attached deposit"
  | depositTooSmall => "ERR_DEPOSIT_TOO_SMALL"
  | notRegistered a => s!"The account {a} is not registered"
  | alreadyRegistered => "The account is already registered"
  | notEnoughBalance => "The account doesn't have enough balance"
  | balanceOverflow => "Nat overflow"
  | totalSupplyOverflow => "Total supply overflow"
  | sameSenderReceiver => "Sender and receiver should be different"
  | amountNotPositive => "The amount should be a positive number"
  | storageDepositTooSmall => "The attached deposit is less than the mimimum storage balance"
  | storageWithdrawPositive => "The amount is greater than the available storage balance"
  | unregisterWithBalance => "Can't unregister the account with the positive balance without force"
  | noPromiseResult => "Accessed invalid promise result index: 0"
  | promiseNotReady => "internal error: entered unreachable code"
  | arithmeticOverflow => "attempt to"

end WNear
