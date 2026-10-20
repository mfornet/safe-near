import Mathlib.Data.Finset.Image
import Model.Borsh
import Model.State
import Model.Env

/-!
# On-chain layout: the view between raw storage and the model

The contract stores borsh(`Contract`) under the key `STATE` and one entry per
registered account under `b"a" ++ borsh(account_id)`. `encode` is the exact
layout; `project` is its (partial) inverse, the "view" of
notes/design/NEAR_MODEL.md. An executable decoder is future work; for proofs the
injectivity of `encode` is what matters.
-/

namespace WNear

open Borsh

/-- Raw contract storage as the runtime sees it: a finite set of key/value pairs
(keys are unique in any real storage). -/
abbrev RawStorage := Finset (Bytes × Bytes)

/-- `near_sdk::env::STATE_KEY`. -/
def stateKey : Bytes := "STATE".toUTF8.toList

/-- `FungibleToken::new(b"a")`: prefix of every `accounts` key. -/
def accountsPrefix : Bytes := "a".toUTF8.toList

/-- Storage key of an account's balance: prefix ++ borsh(`String`). -/
def accountKey (a : AccountId) : Bytes := accountsPrefix ++ Borsh.string a.val

/-- borsh(`Contract { ft: FungibleToken { accounts: LookupMap { key_prefix }, total_supply, account_storage_usage } }`). -/
def header (s : State) : Bytes :=
  Borsh.bytes accountsPrefix ++ Borsh.u128 s.totalSupply ++ Borsh.u64 s.accountStorageUsage

/-- The exact storage of a model state. -/
@[blueprint "def:encode"
  (statement := /-- The storage of a state $s$: the record \texttt{STATE} $\mapsto$ borsh(prefix \texttt{a}, $\mathit{totalSupply}$ as \texttt{u128}, $\mathit{accountStorageUsage}$ as \texttt{u64}) and, for every registered $a$, the record (\texttt{a} followed by borsh$(a)$) $\mapsto$ borsh($\mathit{balance}(a)$ as \texttt{u128}). -/)]
def encode (s : State) : RawStorage :=
  insert (stateKey, header s) (s.registered.image fun a => (accountKey a, Borsh.u128 (s.balance a)))

/-- The view: the well-formed state a raw storage encodes, if any. -/
@[blueprint "def:project"
  (statement := /-- The view: $\mathrm{project}(\mathit{raw})$ is the well-formed state $s$ with $\mathrm{encode}(s) = \mathit{raw}$ when one exists. -/)]
noncomputable def project (raw : RawStorage) : Option State := by
  classical
  exact if h : ∃ s : State, s.WF ∧ encode s = raw then some (Classical.choose h) else none

/-- Bytes the runtime charges for one record. -/
def Config.recordBytes (cfg : Config) (e : Bytes × Bytes) : Nat :=
  e.1.length + e.2.length + cfg.extraBytesPerRecord

/-- `env::storage_usage()` attributable to the contract state. -/
def storageUsage (cfg : Config) (raw : RawStorage) : Nat := ∑ e ∈ raw, cfg.recordBytes e

end WNear
