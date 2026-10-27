import NearRuntime.Types
import NearVM.TrieOverlay
import NearVM.Config

/-!
# Chain state

Everything `apply` reads and writes: accounts, access keys, contract
storage, the receipts postponed until their data arrives, the delayed
receipt queue and the id generator. Maps are association lists: the state
is small in tests and proofs want plain structures.
-/

namespace Near

/-! Association-list helpers. -/
namespace Assoc

def lookup [BEq κ] (m : List (κ × α)) (k : κ) : Option α := (m.find? (·.1 == k)).map (·.2)

def insert [BEq κ] (m : List (κ × α)) (k : κ) (v : α) : List (κ × α) :=
  (k, v) :: m.filter (·.1 != k)

def erase [BEq κ] (m : List (κ × α)) (k : κ) : List (κ × α) := m.filter (·.1 != k)

def contains [BEq κ] (m : List (κ × α)) (k : κ) : Bool := m.any (·.1 == k)

/-- Removing a key that was found strictly decreases the finite map's size.
This also holds for association lists with duplicate keys. -/
theorem erase_length_lt_of_lookup [BEq κ] (m : List (κ × α)) (k : κ) (v : α)
    (h : lookup m k = some v) : (erase m k).length < m.length := by
  unfold lookup at h
  cases hf : m.find? (·.1 == k) with
  | none => simp [hf] at h
  | some entry =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨entry, hm, by simp [bne, hp]⟩

end Assoc

/-- `PromiseYieldTimeout`: a yield of `account` with data id `dataId` times out at block `expiresAt`. -/
structure YieldTimeout where
  account : AccountId
  dataId : Bytes
  expiresAt : Nat
  deriving BEq, Repr, Inhabited

/-- `PromiseYieldStatus`: created, or already resumed by some `promise_yield_resume`. -/
inductive YieldStatus
  | yielded
  | resumeInitiated
  deriving BEq, Repr, Inhabited

structure ChainState where
  accounts : List (AccountId × Account) := []
  accessKeys : List ((AccountId × PublicKey) × AccessKey) := []
  /-- Contract storage per account, key/value pairs. -/
  storage : List (AccountId × List (Bytes × Bytes)) := []
  /-- Action receipts waiting for input data, by receipt id. -/
  postponed : List (ReceiptId × Receipt) := []
  /-- How many input data ids a postponed receipt still waits for. -/
  pendingDataCount : List (ReceiptId × Nat) := []
  /-- Which postponed receipt a data id belongs to. -/
  postponedByData : List (DataId × ReceiptId) := []
  /-- Data received, kept until its receipt consumes it. -/
  receivedData : List (DataId × Option Bytes) := []
  /-- Receipts deferred to a later apply because the gas limit was hit. -/
  delayed : List Receipt := []
  /-- `GlobalContractCode`: the code registered under each global identifier. -/
  globalCode : List (Wasm.GlobalContractId × ContractCode) := []
  /-- `GlobalContractNonce`: the last distribution nonce accepted for an identifier. -/
  globalNonces : List (Wasm.GlobalContractId × Nat) := []
  /-- The nonce lanes of gas keys, keyed by account, public key and lane. -/
  gasKeyNonces : List ((AccountId × PublicKey × Nat) × Nat) := []
  /-- `PromiseYieldIndices`: first and next free index of the timeout queue. `none` until the
  first yield (the column is absent, and reads as `(0, 0)`). -/
  yieldIndices : Option (Nat × Nat) := none
  /-- `PromiseYieldTimeout`: the queue of yields to time out, by index. -/
  yieldTimeouts : List (Nat × YieldTimeout) := []
  /-- `PromiseYieldReceipt`: yielded receipts waiting for their data, by receiver and data id. -/
  yieldReceipts : List ((AccountId × Bytes) × Receipt) := []
  /-- `PromiseYieldStatus` of every yield that has not been resumed or timed out yet. -/
  yieldStatus : List ((AccountId × Bytes) × YieldStatus) := []
  /-- Next receipt / data id. -/
  nextId : Nat := 1
  deriving Inhabited

namespace ChainState

def account? (st : ChainState) (id : AccountId) : Option Account := Assoc.lookup st.accounts id

def setAccount (st : ChainState) (id : AccountId) (a : Account) : ChainState :=
  { st with accounts := Assoc.insert st.accounts id a }

def removeAccount (st : ChainState) (id : AccountId) : ChainState :=
  { st with accounts := Assoc.erase st.accounts id
            accessKeys := st.accessKeys.filter (·.1.1 != id)
            gasKeyNonces := st.gasKeyNonces.filter (·.1.1 != id)
            storage := Assoc.erase st.storage id }

def accessKey? (st : ChainState) (id : AccountId) (pk : PublicKey) : Option AccessKey :=
  Assoc.lookup st.accessKeys (id, pk)

def setAccessKey (st : ChainState) (id : AccountId) (pk : PublicKey) (k : AccessKey) : ChainState :=
  { st with accessKeys := Assoc.insert st.accessKeys (id, pk) k }

def removeAccessKey (st : ChainState) (id : AccountId) (pk : PublicKey) : ChainState :=
  { st with accessKeys := Assoc.erase st.accessKeys (id, pk) }

def contractStorage (st : ChainState) (id : AccountId) : List (Bytes × Bytes) :=
  (Assoc.lookup st.storage id).getD []

def setContractStorage (st : ChainState) (id : AccountId) (s : List (Bytes × Bytes)) : ChainState :=
  { st with storage := Assoc.insert st.storage id s }

def freshId (st : ChainState) : Nat × ChainState := (st.nextId, { st with nextId := st.nextId + 1 })

/-- The code registered under a global identifier. -/
def globalCodeOf? (st : ChainState) (id : Wasm.GlobalContractId) : Option ContractCode :=
  Assoc.lookup st.globalCode id

def setGlobalCode (st : ChainState) (id : Wasm.GlobalContractId) (code : ContractCode) : ChainState :=
  { st with globalCode := Assoc.insert st.globalCode id code }

/-- The distribution nonce of an identifier (absent reads as zero). -/
def globalNonce (st : ChainState) (id : Wasm.GlobalContractId) : Nat :=
  (Assoc.lookup st.globalNonces id).getD 0

def setGlobalNonce (st : ChainState) (id : Wasm.GlobalContractId) (nonce : Nat) : ChainState :=
  { st with globalNonces := Assoc.insert st.globalNonces id nonce }

def setGlobalNonceIf (st : ChainState) (enabled : Bool) (id : Wasm.GlobalContractId) (nonce : Nat) : ChainState :=
  if enabled then st.setGlobalNonce id nonce else st

def gasKeyNonce? (st : ChainState) (id : AccountId) (pk : PublicKey) (lane : Nat) : Option Nat :=
  Assoc.lookup st.gasKeyNonces (id, pk, lane)

def setGasKeyNonce (st : ChainState) (id : AccountId) (pk : PublicKey) (lane nonce : Nat) : ChainState :=
  { st with gasKeyNonces := Assoc.insert st.gasKeyNonces (id, pk, lane) nonce }

def removeGasKeyNonces (st : ChainState) (id : AccountId) (pk : PublicKey) : ChainState :=
  { st with gasKeyNonces := st.gasKeyNonces.filter fun e => !(e.1.1 == id && e.1.2.1 == pk) }

/-- Sum of the balances of an account's gas keys. -/
def gasKeyBalances (st : ChainState) (id : AccountId) : Nat :=
  (st.accessKeys.filter (·.1.1 == id)).foldl
    (fun total e => total + ((e.2.permission.gasKeyInfo?).map (·.1)).getD 0) 0

/-- Gas keys hold balance outside the account (`GasKeyInfo.balance`). -/
def gasKeyFunds (st : ChainState) : Nat :=
  (st.accessKeys.map fun entry => ((entry.2.permission.gasKeyInfo?).map (·.1)).getD 0).sum

/-- Sum of all account balances (amount + locked) and of the balances of gas keys, which hold
funds beside their account. -/
def totalBalance (st : ChainState) : Nat :=
  (st.accounts.map fun (_, a) => a.amount + a.locked).sum + st.gasKeyFunds

end ChainState

/-- The epoch's validator set as `EpochInfoProvider` answers for the chunk: the stake of each
validator, their total, and the minimum stake of `Stake` actions. -/
structure EpochInfo where
  /-- `minimum_stake(prev_block_hash)`: a `Stake` action below it is an `InsufficientStake`. -/
  minimumStake : Nat := 0
  /-- `validator_total_stake(epoch_id)`. -/
  totalStake : Nat := 0
  /-- `validator_stake(epoch_id, account)` for each validator. -/
  validators : List (AccountId × Nat) := []
  deriving Inhabited, Repr

/-- The stake of an account in the epoch, as the `validator_stake` host function reads it
(`bytes` is the account id's UTF-8); zero for an account that is not a validator. -/
def EpochInfo.stake (info : EpochInfo) (bytes : Bytes) : Nat :=
  ((info.validators.find? fun v => v.1.toUTF8.toList == bytes).map (·.2)).getD 0

/-- Per-block context of one `apply`. -/
structure ApplyState where
  /-- Independently constructed complete chunk trie and fresh accounting cache. -/
  storageAccounting : Option TrieOverlay.State := none
  /-- Trusted input: the chunk's recorded storage proof (`recorded_storage_size_upper_bound`) once
  the trie overlay has reached a given state, supplied by the node from its trie recorder.
  Absent, neither storage proof limit is checked (`storageProofFull`, `functionCallContext`). -/
  storageProofSize : Option (TrieOverlay.State → Nat) := none
  /-- On-chain application starts at height one; height zero rejects all nonces. -/
  blockHeight : Nat := 1
  blockTimestamp : Nat := 0
  epochHeight : Nat := 0
  gasPrice : Nat := 100_000_000
  randomSeed : Bytes := List.replicate 32 0
  /-- Some selects native action-derived randomness and requires a valid parent
  binding for every VM call. None retains the trusted direct-seed interface. -/
  nativeReceiptHashes : Option (List (ReceiptId × Bytes)) := none
  /-- Gas burnt in one apply before the remaining receipts are delayed. -/
  gasLimit : Option Nat := none
  /-- The chain's name, which selects the ETH wallet global contract and answers `chain_id`. -/
  chainId : String := ""
  /-- The epoch's validators and minimum stake (`EpochInfoProvider`). -/
  epochInfo : EpochInfo := {}
  /-- The shard being applied and the shards of its layout, for global contract distribution. -/
  shardId : Nat := 0
  shardIds : List Nat := [0]
  /-- Signature check of a `Delegate`/`DelegateV2` action. The runtime does not depend on
  the signature scheme: the caller supplies the verification of the hashed action. Without a
  caller, signatures are trusted like transaction signatures are. -/
  verifyDelegate : Action → Bool := fun _ => true
  deriving Inhabited

end Near
