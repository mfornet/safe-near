import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Model.Types

/-!
# The model of the contract state

On chain the contract is a `FungibleToken` (near-contract-standards 3.1.0):
a `LookupMap<AccountId, u128>` of balances, a `u128` total supply and the
`u64` storage usage of one account entry. The model keeps the same three
pieces of information with mathematical types.
-/

namespace WNear

open Finset

/-- Mainnet storage price. near-sdk 3.1.0 hardcodes it
(`STORAGE_PRICE_PER_BYTE = 10^19` yoctoNEAR); it is not read from the host. -/
def storagePricePerByte : Nat := 10 ^ 19

/-- The contract state. -/
@[blueprint "def:state"
  (statement := /-- The \emph{state} of the contract: a finite set $\mathit{registered}$ of account ids, a balance function $\mathit{balance} : \mathrm{AccountId} \to \mathbb{N}$, the total supply $\mathit{totalSupply} \in \mathbb{N}$ and the per-account storage usage $\mathit{accountStorageUsage} \in \mathbb{N}$. -/)]
structure State where
  /-- Accounts present in the `accounts` map (registered for storage). -/
  registered : Finset AccountId
  /-- wNEAR balance. Meaningful on `registered`; `0` elsewhere when well formed. -/
  balance : AccountId → Nat
  /-- `total_supply`. -/
  totalSupply : Nat
  /-- `account_storage_usage`: bytes one account entry costs, measured at `new`. -/
  accountStorageUsage : Nat

namespace State

/-- Representation bounds: what every decodable on-chain state satisfies. -/
@[blueprint "def:state-wf"
  (statement := /-- A state is \emph{well formed} when unregistered accounts have balance $0$, every balance and the total supply are below $2^{128}$ and the storage usage is below $2^{64}$. -/)]
structure WF (s : State) : Prop where
  unregistered_zero : ∀ a, a ∉ s.registered → s.balance a = 0
  balance_lt : ∀ a, s.balance a < u128Bound
  totalSupply_lt : s.totalSupply < u128Bound
  usage_lt : s.accountStorageUsage < u64Bound

/-- Sum of all balances. -/
@[blueprint "def:supply"
  (statement := /-- $\mathrm{supply}(s) = \sum_{a \in \mathit{registered}} \mathit{balance}(a)$. -/)]
def supply (s : State) : Nat := ∑ a ∈ s.registered, s.balance a

/-- `accounts.get(a).unwrap_or(0)`. -/
def balanceOf (s : State) (a : AccountId) : Nat :=
  if a ∈ s.registered then s.balance a else 0

/-- `storage_balance_bounds().min`: the registration fee. No overflow is possible
(`accountStorageUsage < 2^64` and the price is below `2^64`). -/
@[blueprint "def:storage-min"
  (statement := /-- The registration fee $\mathrm{storageMin}(s) = \mathit{accountStorageUsage} \cdot 10^{19}$ yoctoNEAR (\texttt{storage\_balance\_bounds().min}; near-sdk 3.1.0 hardcodes the byte price). -/)]
def storageMin (s : State) : Nat := s.accountStorageUsage * storagePricePerByte

def setBalance (s : State) (a : AccountId) (b : Nat) : State :=
  { s with balance := Function.update s.balance a b }

/-- `accounts.insert(a, 0)`. -/
def register (s : State) (a : AccountId) : State :=
  { s with registered := insert a s.registered, balance := Function.update s.balance a 0 }

/-- `accounts.remove(a)`. -/
def unregister (s : State) (a : AccountId) : State :=
  { s with registered := s.registered.erase a, balance := Function.update s.balance a 0 }

theorem balanceOf_eq_balance {s : State} (h : s.WF) (a : AccountId) : s.balanceOf a = s.balance a := by
  unfold balanceOf
  split
  · rfl
  · exact (h.unregistered_zero a ‹_›).symm

end State

end WNear
