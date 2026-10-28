import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import NearInterface.Raw
import NearInterface.AccountId
import NearInterface.Config
import NearInterface.TrieOverlay
import NearInterface.StorageProof

/-!
# The function-call action boundary

What varies between two real executions of one function-call action
(`Context`), what such an execution produces (`Observation`), and the
runtime-generic interface between the two (`RuntimeInterface`). Everything is
in the raw space of the protocol: bytes, balances, gas, receipts. A contract
model interprets these values; it does not change them.

The boundary is one function-call action followed by the receipt's
storage-stake check, as nearcore runs a receipt whose only action is that call.
-/

namespace NearInterface

open Wasm Wasm.Near

abbrev Balance := Nat
abbrev Gas := Nat

/-- An account id that nearcore accepts (validity rules v2). Receipts carry
only such ids, so a context never holds anything else. -/
abbrev AccountId := { s : String // validAccountIdBytes s.toUTF8.toList = true }

def AccountId.bytes (a : AccountId) : Bytes := a.val.toUTF8.toList

/-- One account's contract storage: a finite set of key/value records. -/
abbrev RawStorage := Finset (Bytes × Bytes)

/-- One receipt a call creates: receiver, actions, and the indices of earlier
receipts of the same call it waits for. -/
abbrev RawReceipt := ReceiptSpec

/-! ## Storage and balance accounting -/

/-- Bytes a record adds to the account's storage usage
(`storage_usage_config.num_extra_bytes_record` covers the trie overhead). -/
def recordBytes (cfg : RuntimeConfig) (record : Bytes × Bytes) : Nat :=
  record.1.length + record.2.length + cfg.fees.numExtraBytesRecord

/-- Storage usage of the contract records alone. -/
def storageUsageOf (cfg : RuntimeConfig) (raw : RawStorage) : Nat :=
  ∑ record ∈ raw, recordBytes cfg record

/-- Deposit an action takes from the caller's balance at promise creation. -/
def PromiseAction.deposit : PromiseAction → Balance
  | .functionCall _ _ amount _ => amount
  | .transfer amount => amount
  | .transferToGasKey _ amount => amount
  | _ => 0

/-- Total deposit of the receipts a call creates. -/
def receiptDeposits (receipts : List RawReceipt) : Balance :=
  (receipts.map fun r => (r.actions.map PromiseAction.deposit).sum).sum

/-- Pinned nearcore verifier's zero-balance account exemption (NEP-448). -/
def zeroBalanceAccountStorageLimit : Nat := 770

/-- `check_storage_stake`: how much the account lacks to pay for its storage. -/
def stakeDeficit (cfg : RuntimeConfig) (storageUsage amount locked : Nat) : Balance :=
  if storageUsage ≤ zeroBalanceAccountStorageLimit then 0
  else storageUsage * cfg.storageAmountPerByte - amount - locked

/-! ## Context -/

/-- The contract-independent input of one function-call action.

`balance` is `account.amount` before the attached deposit; the VM adds the
deposit when it builds its state. `storageUsage` is the whole account's,
account and code overhead included. `trie` is the full chunk trie with its
node cache: it decides the gas of storage accesses and nothing else. -/
structure Context where
  method : String
  args : Bytes
  current : AccountId
  predecessor : AccountId
  signer : AccountId
  signerPk : Bytes
  attached : Balance
  prepaidGas : Gas
  promiseResults : List PromiseResult
  /-- Receivers of the data this call's result produces (`output_data_receivers`). -/
  outputDataReceivers : List AccountId
  balance : Balance
  locked : Balance
  storageUsage : Nat
  blockHeight : Nat
  timestamp : Nat
  epochHeight : Nat
  randomSeed : Bytes
  trie : Near.TrieOverlay.State
  protocol : RuntimeConfig
  /-- The hash of the executing action, from which `promise_yield_create` derives data ids. -/
  actionHash : Bytes := []
  /-- Data ids of the account's yields that `promise_yield_resume` may resume. -/
  existingYields : List Bytes := []
  /-- The chain's name, for `chain_id`. -/
  chainId : Bytes := []
  /-- `validator_stake`: the stake of the account with these id bytes in the current epoch,
  zero when it is not a validator. -/
  validatorStake : Bytes → Nat := fun _ => 0
  /-- `validator_total_stake`: the current epoch's total validator stake. -/
  validatorTotalStake : Nat := 0
  /-- The receipt's recorded storage proof once the trie reaches a given state, which the
  per-receipt proof limit checks (a trusted input; absent, it is not checked). -/
  storageProofSize : Option (Near.TrieOverlay.State → Nat) := none

/-- Records stored under `account` in a trie view (`TrieKey::ContractData`). -/
def contractData (trie : Near.TrieOverlay.State) (account : Bytes) : RawStorage :=
  let pre := Near.TrieOverlay.contractKey account []
  (trie.view.filterMap fun (key, value) =>
    if pre.isPrefixOf key then some (key.drop pre.length, value) else none).toFinset

/-- What the runtime guarantees about every context it builds: nearcore's
integer widths, storage usage that counts the contract records and leaves
room for one call's growth, and a canonical trie holding the same records.
None of it depends on the call or on the contract. -/
structure Context.WF (ctx : Context) (raw : RawStorage) : Prop where
  balance_lt : ctx.balance + ctx.attached < 2 ^ 128
  locked_lt : ctx.locked < 2 ^ 128
  prepaidGas_lt : ctx.prepaidGas < 2 ^ 64
  blockHeight_lt : ctx.blockHeight < 2 ^ 64
  timestamp_lt : ctx.timestamp < 2 ^ 64
  epochHeight_lt : ctx.epochHeight < 2 ^ 64
  /-- The account's usage counts its contract records. -/
  usage_ge : storageUsageOf ctx.protocol raw ≤ ctx.storageUsage
  /-- Each stored byte burns gas, so one call cannot overflow the `u64` counter. -/
  usage_room : ctx.storageUsage + ctx.protocol.wasm.limits.maxGasBurnt < 2 ^ 64
  /-- Every instruction costs gas: the per-operation and linear base costs are positive. -/
  opCost_pos : 0 < ctx.protocol.wasm.regularOpCost ∧ 0 < ctx.protocol.wasm.linearOpBaseCost
  trie_canonical : Near.TrieConstruction.build ctx.trie.entries = .ok ctx.trie.base
  trie_storage : contractData ctx.trie ctx.current.bytes = raw
  /-- No object of the trie's witness hashes to all zeros, which the trie walk
  reads as the empty trie. A fact about SHA-256 preimages, assumed. -/
  trie_no_zero_hash : List.replicate 32 0 ∉ ctx.trie.base.witness.map Prod.fst
  /-- Contract storage holds one value per key. -/
  raw_keys_unique : ∀ k v v', (k, v) ∈ raw → (k, v') ∈ raw → v = v'
  /-- The trusted recorded-proof size grows only by what the call's storage
  operations record (`Near.TrieOverlay.ProofReach`), as nearcore's recorder does. -/
  proof_growth : ∀ size, ctx.storageProofSize = some size → ∀ t c,
    Near.TrieOverlay.ProofReach ctx.trie t c → size t ≤ size ctx.trie + c

/-- The receipt's recorded storage proof has room for `b` more bytes under
`per_receipt_storage_proof_size_limit`; always, when the proof is not recorded. -/
def Context.ProofRoom (ctx : Context) (b : Nat) : Prop :=
  ∀ size, ctx.storageProofSize = some size →
    size ctx.trie + b ≤ ctx.protocol.wasm.limits.perReceiptStorageProofSizeLimit

/-- The most gas the call can use: its prepaid gas, capped by the per-call burn limit. -/
def Context.gasLimit (ctx : Context) : Gas :=
  min ctx.prepaidGas ctx.protocol.wasm.limits.maxGasBurnt

/-! ## Observation -/

/-- Why a function-call action failed. -/
inductive Failure
  /-- `HostError::GuestPanic`: the message the contract passed to `panic_utf8`. -/
  | panic (msg : String)
  | outOfGas
  /-- The receipt's recorded storage proof passed
  `per_receipt_storage_proof_size_limit` (`HostError::RecordedStorageExceeded`). -/
  | storageProofExceeded
  | balanceExceeded
  | lackBalanceForState (deficit : Balance)
  | methodNotFound
  | other (msg : String)
  /-- An interpreter limitation, not a protocol outcome. -/
  | executionIssue (msg : String)
  deriving DecidableEq, Repr

/-- Everything one function-call action produces. On failure the storage,
balance, usage and receipts are those before the call; burnt gas, logs and
the trie's cache warming survive. -/
structure Observation where
  outcome : Except Failure ReturnData
  storage : RawStorage
  balance : Balance
  storageUsage : Nat
  burntGas : Gas
  usedGas : Gas
  logs : List String
  receipts : List RawReceipt
  trie : Near.TrieOverlay.State

/-- A runtime, seen through one function-call action. -/
structure RuntimeInterface where
  Code : Type
  exec : Code → RawStorage → Context → Observation

end NearInterface
