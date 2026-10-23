import Model.Interface

/-!
# Which inputs are calls

near-sdk 3.1.0's `#[near_bindgen]` wrapper reads a method's arguments with
`serde_json::from_slice` into a struct deriving `Deserialize`, one field per
parameter in declaration order. A method without parameters never reads its
input, so every byte string is a call to it. `Call.decode` is that reading,
on the JSON layer of `NearInterface.Json`; `Parses` is its graph, so it is
functional by construction.
-/

namespace WNear

open NearInterface.Json

/-- A `ValidAccountId` argument. -/
def account (v : Value) : Option AccountId := (accountId v).map AccountId.ofNear

/-- The call `args` sent to `method` deserialises to, if any. -/
def Call.decode (method : String) (args : List UInt8) : Option Call :=
  let fields (names : List String) := (parse args).bind (structFields names)
  match method with
  | "new" => some .new
  | "near_deposit" => some .nearDeposit
  | "ft_total_supply" => some .ftTotalSupply
  | "ft_metadata" => some .ftMetadata
  | "storage_balance_bounds" => some .storageBalanceBounds
  | "storage_minimum_balance" => some .storageMinimumBalance
  | "near_withdraw" => do
    let fs ← fields ["amount"]
    let amount ← required u128 fs[0]?.join
    pure (.nearWithdraw amount)
  | "ft_transfer" => do
    let fs ← fields ["receiver_id", "amount", "memo"]
    let receiver ← required account fs[0]?.join
    let amount ← required u128 fs[1]?.join
    let memo ← optional string fs[2]?.join
    pure (.ftTransfer receiver amount memo)
  | "ft_transfer_call" => do
    let fs ← fields ["receiver_id", "amount", "memo", "msg"]
    let receiver ← required account fs[0]?.join
    let amount ← required u128 fs[1]?.join
    let memo ← optional string fs[2]?.join
    let msg ← required string fs[3]?.join
    pure (.ftTransferCall receiver amount memo msg)
  | "ft_resolve_transfer" => do
    let fs ← fields ["sender_id", "receiver_id", "amount"]
    let sender ← required account fs[0]?.join
    let receiver ← required account fs[1]?.join
    let amount ← required u128 fs[2]?.join
    pure (.ftResolveTransfer sender receiver amount)
  | "ft_balance_of" => do
    let fs ← fields ["account_id"]
    let a ← required account fs[0]?.join
    pure (.ftBalanceOf a)
  | "storage_deposit" => do
    let fs ← fields ["account_id", "registration_only"]
    let a ← optional account fs[0]?.join
    let registrationOnly ← optional bool fs[1]?.join
    pure (.storageDeposit a registrationOnly)
  | "storage_withdraw" => do
    let fs ← fields ["amount"]
    let amount ← optional u128 fs[0]?.join
    pure (.storageWithdraw amount)
  | "storage_unregister" => do
    let fs ← fields ["force"]
    let force ← optional bool fs[0]?.join
    pure (.storageUnregister force)
  | "storage_balance_of" => do
    let fs ← fields ["account_id"]
    let a ← required account fs[0]?.join
    pure (.storageBalanceOf a)
  | _ => none

/-- `args` sent to `method` is a serialisation of `c`. -/
def Parses (method : String) (args : List UInt8) (c : Call) : Prop :=
  Call.decode method args = some c

theorem Parses.functional {method : String} {args : List UInt8} {c c' : Call}
    (h : Parses method args c) (h' : Parses method args c') : c = c' :=
  Option.some.inj (h.symm.trans h')

end WNear
