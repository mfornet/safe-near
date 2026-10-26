import Model.BountyTrie
import Model.Delegation

namespace SputnikDAO2

-- StorageKeys::Delegations is enum tag 2. The legacy LookupMap appends the
-- Borsh AccountId string key and stores a Borsh u128 balance.
def delegationKey (account : String) : BountyBytes :=
  2 :: bountyBorshString account

def encodeDelegationBalance (amount : Nat) : BountyBytes :=
  NearSdk.Borsh.leBytes 16 amount

def parseDelegationBalance (input : BountyBytes) : Option Nat := do
  let (amount, rest) ← NearSdk.BorshParse.natural 16 input
  if rest.isEmpty then some amount else none

abbrev DelegationRawTrie := BountyRawTrie

def delegationRawImage (raw : DelegationRawTrie)
    (state : DelegationState) : Prop :=
  ∀ account,
    raw (delegationKey account) =
      (balanceOf state.balances account).map encodeDelegationBalance

def delegationSerializable (state : DelegationState) : Prop :=
  state.total < 256 ^ 16 ∧
    ∀ account amount, balanceOf state.balances account = some amount →
      amount < 256 ^ 16

def delegationEmptyState : DelegationState :=
  ⟨none, [], 0⟩

def delegationEmptyRaw : DelegationRawTrie := fun _ => none

-- `get_user_weight` and delegation views default an absent key to zero.
def delegationRawBalanceOf (raw : DelegationRawTrie)
    (account : String) : Nat :=
  ((raw (delegationKey account)).bind parseDelegationBalance).getD 0

-- Raw writes performed by each successful source branch. Contract-root
-- serialization of `total_delegation_amount` is a separate obligation.
def delegationRawRegister (raw : DelegationRawTrie)
    (account : String) : DelegationRawTrie :=
  bountyRawWrite raw (delegationKey account) (encodeDelegationBalance 0)

def delegationRawDelegate (raw : DelegationRawTrie)
    (account : String) (newAmount : Nat) : DelegationRawTrie :=
  bountyRawWrite raw (delegationKey account)
    (encodeDelegationBalance newAmount)

end SputnikDAO2
