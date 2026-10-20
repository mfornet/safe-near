import NearRuntime.Types

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

/-- Sum of all account balances (amount + locked). -/
def totalBalance (st : ChainState) : Nat := (st.accounts.map fun (_, a) => a.amount + a.locked).sum

end ChainState

/-- Per-block context of one `apply`. -/
structure ApplyState where
  /-- Independently constructed complete chunk trie and fresh accounting cache. -/
  storageAccounting : Option TrieOverlay.State := none
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
  deriving Inhabited

end Near
