import NearInterface.TrieOverlay

/-!
# The recorded storage proof, as a budget

Since stateless validation, nearcore records every trie node and value a
receipt touches (`TrieRecorder`), and fails a storage operation with
`RecordedStorageExceeded` once the receipt's recorded proof passes
`per_receipt_storage_proof_size_limit`. The proof a call can still record is a
resource of the context, like its gas: earlier actions of the receipt may have
used part of it.

The VM reads the recorded size through a trusted function of the trie
overlay's state (`Context.storageProofSize`). This file bounds how fast that
size can grow, from what nearcore's recorder does (`core/store/src/trie/
trie_recording.rs`):

* a read records, the first time, every node on the key's path and the value
  it dereferences: at most `2·|key| + 2` nodes (a branch consumes one nibble,
  an extension at least one, a leaf ends the path), each at most
  `recordedNodeMax + |key|` bytes as `RawTrieNodeWithSize` (a branch with a
  value is 573 bytes; a leaf or extension holds part of the key);
* a write records nothing until the chunk is finalised;
* a removal of contract data adds 2000 bytes (`record_key_removal`).

`ProofReach s t c` says that the overlay operations the VM performs lead from
`s` to `t` and may record at most `c` bytes. `Context.WF.proof_growth` assumes
the trusted size function respects it, and `Context.ProofRoom` is the budget a
model's `proofBound` is compared with.
-/

namespace Near.TrieOverlay

/-- An upper bound on the serialized size of one recorded trie node, beyond
the key bytes it holds. -/
def recordedNodeMax : Nat := 600

/-- What nearcore records for every removal of contract data. -/
def removalProofCharge : Nat := 2000

/-- The most a lookup of a key of `n` bytes records: every node on its path. -/
def lookupProofBoundLen (n : Nat) : Nat := (2 * n + 2) * (recordedNodeMax + n)

/-- The most a lookup of `key` records. -/
def lookupProofBound (key : List UInt8) : Nat := lookupProofBoundLen key.length

/-- One overlay operation the VM's storage phase performs, and the most the
recorder adds for it. -/
inductive ProofStep : State → State → Nat → Prop
  | lookup {s t : State} {key : List UInt8} {accountNodes : Bool} {p : Option ValuePointer} :
      getReference s key accountNodes = .ok (t, p) → ProofStep s t (lookupProofBound key)
  | dereference {s t : State} {p : ValuePointer} {v : List UInt8} :
      dereference s p = .ok (t, v) → ProofStep s t v.length
  | set (s : State) (key value : List UInt8) : ProofStep s (s.set key value) 0
  | remove (s : State) (key : List UInt8) : ProofStep s (s.remove key) removalProofCharge
  /-- The VM records the trie after billing without changing it. -/
  | same (s : State) : ProofStep s s 0

/-- A sequence of overlay operations and the most it records. -/
inductive ProofReach : State → State → Nat → Prop
  | refl (s : State) : ProofReach s s 0
  | step {s t u : State} {a b : Nat} : ProofStep s t a → ProofReach t u b → ProofReach s u (a + b)

theorem ProofReach.trans {s t u : State} {a b : Nat} (h₁ : ProofReach s t a) (h₂ : ProofReach t u b) :
    ProofReach s u (a + b) := by
  induction h₁ with
  | refl => simpa using h₂
  | step hs _ ih => rw [Nat.add_assoc]; exact .step hs (ih h₂)

theorem ProofReach.mono {s t : State} {a b : Nat} (h : ProofReach s t a) (hab : a ≤ b) :
    ∃ c, c ≤ b ∧ ProofReach s t c := ⟨a, hab, h⟩

end Near.TrieOverlay
