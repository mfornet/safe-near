import NearInterface.TrieConstructionRanks

/-!
# Actual traversal of a locally decoded construction tree

Serialization premises are local node-decoder equations; recursive semantic
premises are absent. Ranks discharge cycle checks only for constructed nodes,
allowing arbitrary value-object aliases. The public-build adapter proving all
local serialization premises remains separate from this traversal layer.
-/
namespace Near.TrieRankedLookup
open TrieAccounting TrieConstruction TrieSerialization TrieConstructionBranch
open TrieBranchConstructionLookup TrieNodeRank TrieConstructionRanks TrieLeaf TrieWitnessTransfer

local macro "unfold_walk" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") "walk"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- A construction tree with local actual decoder certificates. This is proof
input about node encodings, not a premise about any walk or lookup result. -/
inductive Tree : Built → Type where
  | empty : Tree { root := List.replicate 32 0, memoryUsage := 0, witness := [] }
  | leaf (path : List Nat) (value : Bytes) (built : Built)
      (hf : finish ([0] ++ vectorBytes (encodePath true path) ++ valueRefBytes value)
        (100 + 2 * (encodePath true path).length + value.length) [(Sha256.hash value, value)] = .ok built)
      (hd : decodeNode ([0] ++ vectorBytes (encodePath true path) ++ valueRefBytes value ++
        littleEndian 8 (100 + 2 * (encodePath true path).length + value.length)) =
        .ok (.leaf path { length := value.length, hash := Sha256.hash value })) : Tree built
  | extension (path : List Nat) (child built : Built) (tree : Tree child)
      (hf : finish ([3] ++ vectorBytes (encodePath false path) ++ child.root)
        (50 + 2 * (encodePath false path).length + child.memoryUsage) child.witness = .ok built)
      (hd : decodeNode ([3] ++ vectorBytes (encodePath false path) ++ child.root ++
        littleEndian 8 (50 + 2 * (encodePath false path).length + child.memoryUsage)) =
        .ok (.extension path child.root)) : Tree built
  | branch (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) (built : Built)
      (trees : ∀ digit ∈ digits entries, Tree (child digit))
      (hf : finish (branchHeader entries child value) (usage entries child value)
        (branchObjects entries child value) = .ok built)
      (hd : decodeNode (branchHeader entries child value ++ littleEndian 8 (usage entries child value)) =
        .ok (.branch (valueReference value) (references entries child))) : Tree built

theorem Tree.ranked {built : Built} : Tree built → Ranked built
  | .empty => .empty
  | .leaf path value built hf _ => .leaf path value built hf
  | .extension path child built tree hf _ => .extension path child built tree.ranked hf
  | .branch entries child value built trees hf _ =>
      .branch entries child value built (fun digit hd => (trees digit hd).ranked) hf

/-- Reserved-zero is explicit for each real node; the empty tree uses zero. -/
def Tree.Nonzero {built : Built} : Tree built → Prop
  | .empty => True
  | .leaf _ _ built _ _ => built.root ≠ List.replicate 32 0
  | .extension _ _ built tree _ _ => built.root ≠ List.replicate 32 0 ∧ tree.Nonzero
  | .branch _ _ _ built trees _ _ => built.root ≠ List.replicate 32 0 ∧
      ∀ digit hd, (trees digit hd).Nonzero

/-- Pure reference semantics of the certified compressed node tree. -/
def Tree.answer {built : Built} : Tree built → List Nat → Option ValueRef
  | .empty, _ => none
  | .leaf path value _ _ _, key => if path == key then some { length := value.length, hash := Sha256.hash value } else none
  | .extension path _ _ tree _ _, key =>
      if path.isPrefixOf key then tree.answer (key.drop path.length) else none
  | .branch _ _ value _ _ _ _, [] => valueReference value
  | .branch entries _ _ _ trees _ _, digit :: rest =>
      if hd : digit ∈ digits entries then (trees digit hd).answer rest else none

private theorem fetch_of_member (target : Witness) (hc : Consistent target) (root : Hash) (bytes : Bytes)
    (hm : (root, bytes) ∈ target) : fetchObject target root = .ok bytes := by
  apply fetchObject_binding
  cases hf : target.find? (·.1 == root) with
  | none =>
    have h := List.find?_eq_none.mp hf (root, bytes) hm
    simp at h
  | some pair =>
    have hm' := List.mem_of_find?_eq_some hf
    have he : pair.1 = root := by simpa using List.find?_some hf
    have hb : pair.2 = bytes := hc root _ _ (by simpa only [← he] using hm') hm
    simp [hb]

/-- Exact successful-finish projections, used to connect the raw construction
certificate to the containing witness and its ranked ancestor invariant. -/
theorem finish_ready (header : Bytes) (usage : Nat) (objects : Witness) (built : Built)
    (hf : finish header usage objects = .ok built) (target : Witness) (hc : Consistent target)
    (hsub : ∀ pair ∈ built.witness, pair ∈ target) (ancestors : List Hash)
    (ha : RankedAncestors target ancestors built.memoryUsage) :
    fetchObject target built.root = .ok (header ++ littleEndian 8 usage) ∧
      ancestors.contains built.root = false ∧ built.memoryUsage = usage ∧
      built.witness.length = objects.length + 1 ∧ NodeBinding target built.root built.memoryUsage := by
  have ht := finish_nodeBinding header usage objects built hf
  have he := finish_parts header usage objects (by obtain ⟨_, _, hroom⟩ := ht.1; exact hroom)
  have hb := Except.ok.inj (hf.symm.trans he)
  have hm : (built.root, header ++ littleEndian 8 usage) ∈ built.witness := by rw [hb]; exact List.mem_cons_self
  have hn : NodeBinding target built.root built.memoryUsage := by
    rw [ht.2]
    exact nodeBinding_mono _ _ _ _ hsub ht.1
  have hcycle := ranked_ancestors_exclude target hc ancestors built.root built.memoryUsage ha hn
  refine ⟨fetch_of_member target hc built.root _ (hsub _ hm), by simpa using hcycle, ht.2, ?_, hn⟩
  rw [hb]
  simp

/-- Recursive actual traversal returns the pure tree's reference. No child
walk equation is assumed: induction runs each selected subtree in the same
containing witness, deriving cycle safety from strict node ranks. -/
theorem walk_answer {built : Built} (tree : Tree built) (hz : tree.Nonzero)
    (target : Witness) (hc : Consistent target) (hsub : ∀ pair ∈ built.witness, pair ∈ target)
    (ancestors : List Hash) (ha : RankedAncestors target ancestors built.memoryUsage)
    (accountNodes : Bool) (fuel : Nat) (hroom : built.witness.length < fuel)
    (key : List Nat) (state : Accounting) :
    ∃ after, walkObjects target accountNodes fuel ancestors built.root key state = .ok (tree.answer key, after) := by
  induction tree generalizing target ancestors fuel key state with
  | empty =>
    cases fuel with
    | zero => simp at hroom
    | succ fuel =>
      refine ⟨state, ?_⟩
      unfold walkObjects
      unfold_walk
      simp only [beq_self_eq_true, ↓reduceIte, pure, Except.pure, Tree.answer]
  | leaf path value built hf hd =>
    have hp := finish_ready _ _ _ _ hf target hc hsub ancestors ha
    cases fuel with
    | zero => omega
    | succ fuel =>
      refine ⟨if accountNodes then state.touch built.root "node" else state, ?_⟩
      unfold walkObjects
      unfold_walk
      have hfetch := hp.1
      unfold fetchObject at hfetch
      simp only [beq_eq_false_iff_ne.mpr hz, Bool.false_eq_true, ↓reduceIte, hp.2.1,
        hfetch, hd, bind, Except.bind, pure, Except.pure, Tree.answer]
  | extension path child built tree hf hd ih =>
    have hp := finish_ready _ _ _ _ hf target hc hsub ancestors ha
    have hchild : ∀ pair ∈ child.witness, pair ∈ target := fun pair hm =>
      hsub pair (finish_objects_subset _ _ _ _ hf pair hm)
    have hrank : RankedAncestors target (built.root :: ancestors) child.memoryUsage := by
      apply ranked_ancestors_descend target ancestors built.root built.memoryUsage child.memoryUsage ha hp.2.2.2.2
      rw [hp.2.2.1]
      omega
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hcfuel : child.witness.length < fuel := by rw [hp.2.2.2.1] at hroom; omega
      rw [TrieExtension.walkObjects_extension target built.root child.root _ path key state ancestors
        accountNodes fuel hz.1 hp.2.1 hp.1 hd]
      cases hprefix : path.isPrefixOf key with
      | false =>
        refine ⟨if accountNodes then state.touch built.root "node" else state, ?_⟩
        simp only [hprefix, Bool.false_eq_true, ↓reduceIte, Tree.answer]
      | true =>
        obtain ⟨after, hr⟩ := ih hz.2 target hc hchild (built.root :: ancestors) hrank fuel hcfuel
          (key.drop path.length) (if accountNodes then state.touch built.root "node" else state)
        exact ⟨after, by simpa only [hprefix, ↓reduceIte, Tree.answer] using hr⟩
  | branch entries child value built trees hf hd ih =>
    have hp := finish_ready _ _ _ _ hf target hc hsub ancestors ha
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [TrieBranchLookup.walkObjects_branch target built.root _ (valueReference value) (references entries child)
        key state ancestors accountNodes fuel hz.1 hp.2.1 hp.1 hd]
      cases key with
      | nil => exact ⟨_, rfl⟩
      | cons digit rest =>
        simp only [references]
        rw [find_mapped_digits]
        by_cases hm : digit ∈ digits entries
        · simp only [hm, ↓reduceIte]
          have hchild : ∀ pair ∈ (child digit).witness, pair ∈ target := by
            intro pair hp'
            apply hsub
            apply finish_objects_subset _ _ _ _ hf
            apply List.mem_append_right
            exact List.mem_flatMap.mpr ⟨digit, hm, hp'⟩
          have hlen : (child digit).witness.length ≤ (branchObjects entries child value).length := by
            obtain ⟨left, right, hs⟩ := List.mem_iff_append.mp hm
            simp only [branchObjects, hs, List.flatMap_append, List.flatMap_cons, List.length_append]
            omega
          have hcfuel : (child digit).witness.length < fuel := by rw [hp.2.2.2.1] at hroom; omega
          have hrank : RankedAncestors target (built.root :: ancestors) (child digit).memoryUsage := by
            apply ranked_ancestors_descend target ancestors built.root built.memoryUsage _ ha hp.2.2.2.2
            rw [hp.2.2.1]
            exact branch_child_usage_lt entries child value digit hm
          obtain ⟨after, hr⟩ := ih digit hm (hz.2 digit hm) target hc hchild (built.root :: ancestors)
            hrank fuel hcfuel rest (if accountNodes then state.touch built.root "node" else state)
          exact ⟨after, by simpa only [Tree.answer, hm, ↓reduceDIte] using hr⟩
        · refine ⟨if accountNodes then state.touch built.root "node" else state, ?_⟩
          simp only [hm, ↓reduceIte, Tree.answer, ↓reduceDIte]

/-- Root width follows actual finish hashing, including the empty sentinel. -/
theorem Tree.root_width {built : Built} (tree : Tree built) : built.root.length = 32 := by
  have finish_width : ∀ header usage objects built, finish header usage objects = .ok built → built.root.length = 32 := by
    intro header usage objects built hf
    have ht := finish_nodeBinding header usage objects built hf
    obtain ⟨_, _, hroom⟩ := ht.1
    have he := Except.ok.inj (hf.symm.trans (finish_parts header usage objects hroom))
    rw [he]
    exact Sha256.hash_length _
  cases tree with
  | empty => rfl
  | leaf path value built hf hd => exact finish_width _ _ _ _ hf
  | extension path child built tree hf hd => exact finish_width _ _ _ _ hf
  | branch entries child value built trees hf hd => exact finish_width _ _ _ _ hf

/-- Construct a local leaf decoder certificate from ordinary encoding bounds. -/
def Tree.ofLeaf (path : List Nat) (value : Bytes) (built : Built)
    (hf : finish ([0] ++ vectorBytes (encodePath true path) ++ valueRefBytes value)
      (100 + 2 * (encodePath true path).length + value.length) [(Sha256.hash value, value)] = .ok built)
    (hpath : ValidPath path) (hpathRoom : (encodePath true path).length < 2 ^ 32)
    (hvalue : value.length < 2 ^ 32) : Tree built :=
  .leaf path value built hf (decodeNode_leaf path value _ hpath hpathRoom hvalue
    (by obtain ⟨_, _, hroom⟩ := (finish_nodeBinding _ _ _ _ hf).1; exact hroom))

/-- Child hash width and parent usage width follow actual construction;
only compact-path validity/width remain local input obligations. -/
def Tree.ofExtension (path : List Nat) (child built : Built) (tree : Tree child)
    (hf : finish ([3] ++ vectorBytes (encodePath false path) ++ child.root)
      (50 + 2 * (encodePath false path).length + child.memoryUsage) child.witness = .ok built)
    (hpath : ValidPath path) (hnonempty : path ≠ [])
    (hpathRoom : (encodePath false path).length < 2 ^ 32) : Tree built :=
  .extension path child built tree hf (TrieExtension.decodeNode_extension path child.root _ hpath hnonempty
    hpathRoom tree.root_width
    (by obtain ⟨_, _, hroom⟩ := (finish_nodeBinding _ _ _ _ hf).1; exact hroom))

/-- Branch child widths and parent u64 rank are derived, rather than supplied
as independent assumptions. The branch's optional value needs its u32 bound. -/
def Tree.ofBranch (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) (built : Built)
    (trees : ∀ digit ∈ digits entries, Tree (child digit))
    (hf : finish (branchHeader entries child value) (usage entries child value)
      (branchObjects entries child value) = .ok built)
    (hvalue : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32) : Tree built :=
  .branch entries child value built trees hf (nodeBytes_decode entries child value
    (by intro digit hm ha; exact (trees digit (by simpa [digits] using And.intro hm ha)).root_width)
    hvalue (by obtain ⟨_, _, hroom⟩ := (finish_nodeBinding _ _ _ _ hf).1; exact hroom))

/-- Reference-only actual public lookup follows the tree semantics, with all
recursive traversal and rank-based cycle checks already discharged. -/
theorem lookup_answer_reference {built : Built} (tree : Tree built) (hz : tree.Nonzero)
    (hc : Consistent built.witness) (previous : Accounting) (query : Query)
    (hmode : query.dereference = false) :
    ∃ after, lookup built.witness built.root previous query = .ok {
      reference := tree.answer (nibbles query.key), value := none, state := after } := by
  obtain ⟨after, hw⟩ := walk_answer tree hz built.witness hc (fun _ hm => hm) []
    (by intro _ hm; cases hm) query.accountNodes (built.witness.length + 1) (by omega)
    (nibbles query.key) (queryStart previous query)
  refine ⟨after, ?_⟩
  unfold walkObjects queryStart at hw
  simp only [lookup, hw, bind, Except.bind]
  cases hr : tree.answer (nibbles query.key) <;> simp [hmode, pure, Except.pure]

/-- Actual public build collision-checking provides consistency and its
possibly smaller final default fuel. No recursive lookup premise remains:
the only tree input consists of local constructor/decoder certificates. -/
theorem build_lookup_answer_reference (entries : List (Bytes × Bytes)) (built raw : Built)
    (hb : build entries = .ok built)
    (hconstruct : construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw)
    (tree : Tree raw) (hz : tree.Nonzero) (previous : Accounting) (query : Query)
    (hmode : query.dereference = false) :
    ∃ after, lookup built.witness built.root previous query = .ok {
      reference := tree.answer (nibbles query.key), value := none, state := after } := by
  have hc := (TrieConstructionInvariant.build_raw_checked entries built raw hb hconstruct).2.1
  obtain ⟨after, hr⟩ := lookup_answer_reference tree hz hc previous query hmode
  exact ⟨after, TrieWitnessFuel.build_lookup_transfer entries built raw hb hconstruct previous query _ hr⟩

end Near.TrieRankedLookup
