import NearSdk.BorshParse

/-!
# near-contract-standards `FungibleToken` storage, decoded and checked

The persistent layout of `FungibleToken` (wNEAR and nearcore's fungible-token test contract
use it): `STATE` starts with borsh(`accounts` key prefix), the `u128` total supply and the `u64`
storage usage of one account; each balance is a `u128` under the prefix followed by
borsh(account id). `decode` reads a contract's raw storage and `check` decides the token
invariant on it, as wNEAR's `Inv` states it: every balance and the supply fit a `u128`, the
usage fits a `u64`, and the balances sum to the total supply.
-/

namespace NearSdk.FungibleToken
open NearSdk.Borsh NearSdk.BorshParse

/-- A decoded token. Keys of the contract's storage that are neither `STATE` nor under the
accounts prefix (metadata, other fields) are kept, counted, as `others`. -/
structure Token where
  accountsPrefix : Bytes
  totalSupply : Nat
  accountStorageUsage : Nat
  balances : List (String × Nat)
  others : Nat
  deriving Repr

/-- `near_sdk::env::STATE_KEY`. -/
def stateKey : Bytes := "STATE".toUTF8.toList

/-- The `FungibleToken` fields at the start of `STATE`; later fields of the contract follow. -/
def header : Parser (Bytes × Nat × Nat) := fun input => do
  let (pre, rest) ← BorshParse.bytes input
  let (supply, rest) ← natural 16 rest
  let (usage, rest) ← natural 8 rest
  pure ((pre, supply, usage), rest)

/-- Decode a contract's raw storage (`key ↦ value`). -/
def decode (storage : List (Bytes × Bytes)) : Except String Token := do
  let some (_, state) := storage.find? (·.1 == stateKey) | throw "no STATE record"
  let some ((pre, totalSupply, accountStorageUsage), _) := header state
    | throw "STATE does not start with a FungibleToken"
  let mut balances := []
  let mut others := 0
  for (key, value) in storage do
    if key == stateKey then continue
    if pre.isPrefixOf key then
      let some account := exact text (key.drop pre.length)
        | throw s!"key under the accounts prefix is not a borsh account id: {key}"
      let some balance := exact (natural 16) value
        | throw s!"balance of {account} is not a u128"
      balances := balances ++ [(account, balance)]
    else
      others := others + 1
  return { accountsPrefix := pre, totalSupply, accountStorageUsage, balances, others }

/-- The token invariant, decided: the reasons it fails, empty when it holds. -/
def violations (t : Token) (expectedUsage : Option Nat := none) : List String :=
  let sum := (t.balances.map (·.2)).sum
  (if t.totalSupply < 2 ^ 128 then [] else ["total supply does not fit a u128"]) ++
  (if t.accountStorageUsage < 2 ^ 64 then [] else ["account storage usage does not fit a u64"]) ++
  (t.balances.filter (·.2 ≥ 2 ^ 128)).map (fun (a, _) => s!"balance of {a} does not fit a u128") ++
  (if (t.balances.map (·.1)).Nodup then [] else ["an account appears twice"]) ++
  (if sum = t.totalSupply then [] else [s!"balances sum to {sum}, total supply is {t.totalSupply}"]) ++
  (match expectedUsage with
    | some u => if t.accountStorageUsage = u then [] else
        [s!"account storage usage is {t.accountStorageUsage}, expected {u}"]
    | none => [])

/-- The invariant holds exactly when there is no violation; in particular the supply is the
sum of the balances. -/
theorem supply_of_violations_nil {t : Token} {u : Option Nat} (h : violations t u = []) :
    (t.balances.map (·.2)).sum = t.totalSupply := by
  unfold violations at h
  simp only [List.append_eq_nil_iff] at h
  have h5 := h.1.2
  by_cases hne : (t.balances.map (·.2)).sum = t.totalSupply
  · exact hne
  · simp [hne] at h5

end NearSdk.FungibleToken
