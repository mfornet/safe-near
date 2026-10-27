import NearInterface.TrieWitnessFuel

/-!
# Node-only rank separation

Every constructed node ends in its subtree's u64 memory usage. Consistent
object bindings therefore prohibit a hash alias between nodes of different
rank. Value objects need not be excluded from ancestor hashes. Reserved zero
hashes remain a separate condition, since the runtime treats zero as absence.
-/
namespace Near.TrieNodeRank
open TrieAccounting TrieConstruction TrieSerialization TrieConstructionBranch
open TrieBranchConstructionLookup TrieWitnessTransfer

local macro "unfold_finish" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "finish"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- A node's actual object binding carries its bounded serialized usage rank. -/
def NodeBinding (witness : Witness) (root : Hash) (usage : Nat) : Prop :=
  ∃ header, (root, header ++ littleEndian 8 usage) ∈ witness ∧ usage < 2 ^ 64

/-- Equal serialized nodes have equal u64 rank, regardless of header length. -/
theorem suffix_usage_injective (first second : Bytes) (a b : Nat)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (he : first ++ littleEndian 8 a = second ++ littleEndian 8 b) : a = b := by
  have hl : first.length = second.length := by
    have h := congrArg List.length he
    simp only [List.length_append, littleEndian_length] at h
    omega
  have hs := congrArg (List.drop first.length) he
  have ht : littleEndian 8 a = littleEndian 8 b := by
    simp only [List.drop_append, List.drop_length, List.nil_append,
      Nat.sub_self, List.drop_zero] at hs
    simpa only [hl, List.drop_length, Nat.sub_self, List.drop_zero, List.nil_append] using hs
  have hv := congrArg (fun bytes : Bytes => bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0) ht
  simpa only [littleEndian_value8 a ha, littleEndian_value8 b hb] using hv

/-- Rank equality is forced only for node bindings; no property of arbitrary
value-object payloads or cryptographic injectivity is assumed. -/
theorem equal_hash_rank (witness : Witness) (hc : Consistent witness) (root : Hash) (a b : Nat)
    (ha : NodeBinding witness root a) (hb : NodeBinding witness root b) : a = b := by
  obtain ⟨first, hf, haroom⟩ := ha
  obtain ⟨second, hs, hbroom⟩ := hb
  exact suffix_usage_injective first second a b haroom hbroom (hc root _ _ hf hs)

theorem strict_rank_ne (witness : Witness) (hc : Consistent witness) (parent child : Hash)
    (a b : Nat) (ha : NodeBinding witness parent a) (hb : NodeBinding witness child b)
    (hlt : b < a) : child ≠ parent := by
  intro he
  subst child
  have := equal_hash_rank witness hc parent a b ha hb
  omega

/-- Node bindings are retained when their raw object list is included. -/
theorem nodeBinding_mono (source target : Witness) (root : Hash) (usage : Nat)
    (hsub : ∀ pair ∈ source, pair ∈ target) (hb : NodeBinding source root usage) :
    NodeBinding target root usage := by
  obtain ⟨header, hm, hr⟩ := hb
  exact ⟨header, hsub _ hm, hr⟩

/-- A local actual successful finish supplies the serialized node binding and
its u64 bound. This applies uniformly to leaf, extension and branch nodes. -/
theorem finish_nodeBinding (header : Bytes) (usage : Nat) (objects : Witness) (built : Built)
    (hfinish : finish header usage objects = .ok built) :
    NodeBinding built.witness built.root usage ∧ built.memoryUsage = usage := by
  unfold finish at hfinish
  unfold_finish
  split at hfinish
  · cases hfinish
  · simp only [pure, Except.pure, Except.ok.injEq] at hfinish
    subst built
    exact ⟨⟨header, by simp [littleEndian], by omega⟩, rfl⟩

/-- Each selected branch child's usage is strictly below the actual parent
usage, including value-bearing branches. -/
theorem branch_child_usage_lt (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (digit : Nat) (hactive : digit ∈ digits entries) :
    (child digit).memoryUsage < usage entries child value := by
  obtain ⟨left, right, hs⟩ := List.mem_iff_append.mp hactive
  unfold usage
  rw [hs, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

/-- The branch's root object is first, with precisely the parent usage suffix. -/
theorem branch_nodeBinding (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (hroom : usage entries child value < 2 ^ 64) :
    NodeBinding (branchBuilt entries child value).witness (branchBuilt entries child value).root
      (usage entries child value) := by
  refine ⟨(match value with | none => [1] | some bytes => [2] ++ valueRefBytes bytes) ++
      littleEndian 2 (TrieBitmap.maskOf (TrieBitmap.groupActive entries) 16) ++
      (digits entries).flatMap (fun digit => (child digit).root), ?_, hroom⟩
  cases value <;> simp [branchBuilt, nodeBytes, List.append_assoc]

/-- Actual parent concatenation lifts an isolated child's node binding; strict
usage then excludes the parent hash at that child node only. Arbitrary child
value objects may still alias the parent without entering this premise. -/
theorem branch_child_root_ne (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (digit : Nat) (hactive : digit ∈ digits entries)
    (hc : Consistent (branchBuilt entries child value).witness)
    (hroom : usage entries child value < 2 ^ 64)
    (hchild : NodeBinding (child digit).witness (child digit).root (child digit).memoryUsage) :
    (child digit).root ≠ (branchBuilt entries child value).root := by
  apply strict_rank_ne (branchBuilt entries child value).witness hc _ _
    (usage entries child value) (child digit).memoryUsage (branch_nodeBinding entries child value hroom)
  · apply nodeBinding_mono _ _ _ _ _ hchild
    obtain ⟨front, suffix, hs, _⟩ := branch_child_segment entries child value digit hactive
    intro pair hm
    rw [hs]
    exact List.mem_append_left _ (List.mem_append_right _ hm)
  · exact branch_child_usage_lt entries child value digit hactive

/-- Every bound descendant node lies strictly below the parent branch. This
condition applies to node bindings, including a descendant whose hash also
occurs as a value object; it does not exclude all value-object hashes. -/
theorem branch_descendant_ne (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (digit : Nat) (hactive : digit ∈ digits entries)
    (hc : Consistent (branchBuilt entries child value).witness)
    (hroom : usage entries child value < 2 ^ 64) (descendant : Hash) (rank : Nat)
    (hnode : NodeBinding (child digit).witness descendant rank)
    (hrank : rank ≤ (child digit).memoryUsage) :
    descendant ≠ (branchBuilt entries child value).root := by
  apply strict_rank_ne (branchBuilt entries child value).witness hc _ _
    (usage entries child value) rank (branch_nodeBinding entries child value hroom)
  · apply nodeBinding_mono _ _ _ _ _ hnode
    obtain ⟨front, suffix, hs, _⟩ := branch_child_segment entries child value digit hactive
    intro pair hm
    rw [hs]
    exact List.mem_append_left _ (List.mem_append_right _ hm)
  · exact Nat.lt_of_le_of_lt hrank (branch_child_usage_lt entries child value digit hactive)

/-- An extension's actual finish includes the child witness and a positive
usage overhead. Every child node within the child's rank bound therefore
avoids the parent hash, even if unrelated child values alias that hash. -/
theorem extension_descendant_ne (header encoded : Bytes) (child built : Built)
    (hfinish : finish header (50 + 2 * encoded.length + child.memoryUsage) child.witness = .ok built)
    (hc : Consistent built.witness) (descendant : Hash) (rank : Nat)
    (hnode : NodeBinding child.witness descendant rank) (hrank : rank ≤ child.memoryUsage) :
    descendant ≠ built.root := by
  have hp := finish_nodeBinding header (50 + 2 * encoded.length + child.memoryUsage)
    child.witness built hfinish
  have hsub : ∀ pair ∈ child.witness, pair ∈ built.witness := by
    unfold finish at hfinish
    unfold_finish
    split at hfinish
    · cases hfinish
    · simp only [pure, Except.pure, Except.ok.injEq] at hfinish
      subst built
      exact fun pair hm => List.mem_cons_of_mem _ hm
  exact strict_rank_ne built.witness hc built.root descendant _ rank hp.1
    (nodeBinding_mono _ _ _ _ hsub hnode) (by omega)

/-- Proof-facing path invariant: every recorded ancestor is a node with a
strictly larger serialized usage rank than the current subtree bound. -/
def RankedAncestors (witness : Witness) (ancestors : List Hash) (rank : Nat) : Prop :=
  ∀ ancestor ∈ ancestors, ∃ parentRank, NodeBinding witness ancestor parentRank ∧ rank < parentRank

/-- Consistent actual object bindings turn rank descent into precisely the
reader's ancestor-cycle exclusion, without excluding arbitrary value hashes. -/
theorem ranked_ancestors_exclude (witness : Witness) (hc : Consistent witness)
    (ancestors : List Hash) (root : Hash) (rank : Nat)
    (ha : RankedAncestors witness ancestors rank) (hn : NodeBinding witness root rank) :
    root ∉ ancestors := by
  intro hm
  obtain ⟨parentRank, hp, hlt⟩ := ha root hm
  have := equal_hash_rank witness hc root rank parentRank hn hp
  omega

/-- Traversing to a smaller subtree extends the invariant with the actual
current node. This supports arbitrary depth, not only direct parent/child. -/
theorem ranked_ancestors_descend (witness : Witness) (ancestors : List Hash) (root : Hash)
    (rank childRank : Nat) (ha : RankedAncestors witness ancestors rank)
    (hn : NodeBinding witness root rank) (hlt : childRank < rank) :
    RankedAncestors witness (root :: ancestors) childRank := by
  intro ancestor hm
  rcases List.mem_cons.mp hm with he | hm
  · subst ancestor
    exact ⟨rank, hn, hlt⟩
  · obtain ⟨parentRank, hp, hparent⟩ := ha ancestor hm
    exact ⟨parentRank, hp, Nat.lt_trans hlt hparent⟩

end Near.TrieNodeRank
