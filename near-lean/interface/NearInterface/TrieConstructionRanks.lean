import NearInterface.TrieNodeRank

/-! Structural rank certificates extracted from actual successful construction.
No predicate is imposed on arbitrary value objects. Nonzero node roots are
not inferred from hashes or construction success. -/
namespace Near.TrieConstructionRanks
open TrieAccounting TrieConstruction TrieSerialization TrieConstructionBranch
open TrieBranchConstructionLookup TrieNodeRank

local macro "unfold_construct" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "construct"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

local macro "unfold_construct_lhs" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "construct"
  `(tactic| conv => lhs; unfold construct; unfold $(Lean.mkIdent actual))

local macro "unfold_finish" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "finish"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- The exact node header before the common u64 usage trailer. -/
def branchHeader (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) : Bytes :=
  (match value with | none => [1] | some bytes => [2] ++ valueRefBytes bytes) ++
    littleEndian 2 (TrieBitmap.maskOf (TrieBitmap.groupActive entries) 16) ++
    (digits entries).flatMap (fun digit => (child digit).root)

def branchObjects (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) : Witness :=
  (match value with | none => [] | some bytes => [(Sha256.hash bytes, bytes)]) ++
    (digits entries).flatMap (fun digit => (child digit).witness)

/-- Recursive node certificates retain actual finish equations, child
certificates, and the exact positive usage overhead at each node kind. -/
inductive Ranked : Built → Prop where
  | empty : Ranked { root := List.replicate 32 0, memoryUsage := 0, witness := [] }
  | leaf (path : List Nat) (value : Bytes) (built : Built)
      (hfinish : finish ([0] ++ vectorBytes (encodePath true path) ++ valueRefBytes value)
        (100 + 2 * (encodePath true path).length + value.length) [(Sha256.hash value, value)] = .ok built) :
      Ranked built
  | extension (path : List Nat) (child built : Built) (hchild : Ranked child)
      (hfinish : finish ([3] ++ vectorBytes (encodePath false path) ++ child.root)
        (50 + 2 * (encodePath false path).length + child.memoryUsage) child.witness = .ok built) :
      Ranked built
  | branch (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) (built : Built)
      (hchildren : ∀ digit ∈ digits entries, Ranked (child digit))
      (hfinish : finish (branchHeader entries child value) (usage entries child value)
        (branchObjects entries child value) = .ok built) : Ranked built

/-- A successful loop cannot conceal an unsuccessful selected child action. -/
theorem loop_children (active : Nat → Bool) (action : Nat → Except String Built)
    (selected : List Nat) (acc after : Acc)
    (hr : forIn selected acc (loopStep active action) = .ok after) :
    ∀ digit ∈ selected, active digit = true → ∃ built, action digit = .ok built := by
  induction selected generalizing acc with
  | nil => simp
  | cons digit selected ih =>
    rw [List.forIn_cons] at hr
    cases hp : active digit
    · simp only [loopStep, hp, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at hr
      intro next hn ha
      rcases List.mem_cons.mp hn with he | hn
      · subst next; simp_all
      · exact ih acc hr next hn ha
    · cases hc : action digit with
      | error error =>
        simp only [loopStep, hp, ↓reduceIte, hc, bind, Except.bind] at hr
        cases hr
      | ok child =>
        simp only [loopStep, hp, ↓reduceIte, hc, bind, Except.bind, pure, Except.pure] at hr
        intro next hn ha
        rcases List.mem_cons.mp hn with he | hn
        · subst next; exact ⟨child, hc⟩
        · exact ih _ hr next hn ha

/-- Successful branch-loop execution supplies actual results for all selected
recursive calls. The function is chosen from those results, not postulated. -/
theorem branchLoop_children (fuel : Nat) (entries : List (List Nat × Bytes)) (acc : Acc)
    (hr : branchLoop fuel entries = .ok acc) :
    ∃ child : Nat → Built, ∀ digit ∈ List.range 16, TrieBitmap.groupActive entries digit = true →
      childAction fuel entries digit = .ok (child digit) := by
  unfold branchLoop at hr
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hr
  change forIn (List.range' 0 16) _ _ = _ at hr
  rw [← List.range_eq_range'] at hr
  have ht := loop_children _ _ _ _ _ hr
  classical
  have he : ∀ digit, ∃ built, digit ∈ List.range 16 → TrieBitmap.groupActive entries digit = true →
      childAction fuel entries digit = .ok built := by
    intro digit
    by_cases h : digit ∈ List.range 16 ∧ TrieBitmap.groupActive entries digit = true
    · obtain ⟨built, hb⟩ := ht digit h.1 h.2
      exact ⟨built, fun _ _ => hb⟩
    · exact ⟨{ root := [], memoryUsage := 0, witness := [] }, by intro hm ha; exact False.elim (h ⟨hm, ha⟩)⟩
  exact ⟨fun digit => Classical.choose (he digit), fun digit => Classical.choose_spec (he digit)⟩

/-- The actual recursive constructor's multi-entry equation, exposing both
extension recursion and the branch loop before assuming either succeeds. -/
theorem construct_many (fuel : Nat) (first second : List Nat × Bytes)
    (rest : List (List Nat × Bytes)) :
    construct (fuel + 1) (first :: second :: rest) =
      (let shared := (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1
       if !shared.isEmpty then do
         let child ← construct fuel ((first :: second :: rest).map fun (key, value) =>
           (key.drop shared.length, value))
         let encoded := encodePath false shared
         if encoded.length ≥ 2 ^ 32 then throw "trie compact path exceeds u32"
         return ← finish ([3] ++ vectorBytes encoded ++ child.root)
           (50 + 2 * encoded.length + child.memoryUsage) child.witness
       else do
         let acc ← branchLoop fuel (first :: second :: rest)
         match ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd with
         | none => return ← finish ([1] ++ littleEndian 2 acc.1 ++ acc.2.1) acc.2.2.2 acc.2.2.1
         | some value => return ← finish ([2] ++ valueRefBytes value ++ littleEndian 2 acc.1 ++ acc.2.1) (acc.2.2.2 + 50 + value.length) ((Sha256.hash value, value) :: acc.2.2.1)) := by
  unfold_construct_lhs
  simp only
  change (if !((second :: rest).foldl (fun path entry => commonPath path entry.1) first.1).isEmpty then _ else _) = _
  split
  · rfl
  · unfold branchLoop
    congr 1
    funext acc
    cases hv : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd <;> rfl

/-- Every successful actual recursive construction has a structural node-rank
certificate. Recursive children are recovered from actual branch execution. -/
theorem construct_ranked (fuel : Nat) (entries : List (List Nat × Bytes)) (built : Built)
    (hr : construct fuel entries = .ok built) : Ranked built := by
  induction fuel generalizing entries built with
  | zero =>
    unfold construct at hr
    unfold_construct
    cases hr
  | succ fuel ih =>
    cases entries with
    | nil =>
      have he : construct (fuel + 1) [] = .ok { root := List.replicate 32 0, memoryUsage := 0, witness := [] } := rfl
      rw [he] at hr
      cases Except.ok.inj hr
      exact .empty
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨path, value⟩ := first
        change (if (encodePath true path).length ≥ 2 ^ 32 then
          .error "trie compact path exceeds u32" else
          finish ([0] ++ vectorBytes (encodePath true path) ++ valueRefBytes value)
            (100 + 2 * (encodePath true path).length + value.length) [(Sha256.hash value, value)]) = .ok built at hr
        split at hr
        · cases hr
        · exact .leaf path value built hr
      | cons second rest =>
        rw [construct_many] at hr
        dsimp only at hr
        split at hr
        · cases hc : construct fuel ((first :: second :: rest).map fun (key, value) =>
              (key.drop ((second :: rest).foldl (fun path entry => commonPath path entry.1) first.1).length, value)) with
          | error error => simp only [hc, bind, Except.bind] at hr; cases hr
          | ok child =>
            simp only [hc, bind, Except.bind] at hr
            split at hr
            · change Except.error _ = Except.ok _ at hr; cases hr
            · exact .extension _ child built (ih _ child hc) hr
        · cases hl : branchLoop fuel (first :: second :: rest) with
          | error error => simp only [hl, bind, Except.bind] at hr; cases hr
          | ok acc =>
            obtain ⟨child, hchild⟩ := branchLoop_children fuel (first :: second :: rest) acc hl
            have he := branchLoop_contract fuel (first :: second :: rest) child hchild
            rw [hl] at he
            have heq := Except.ok.inj he
            subst acc
            simp only [hl, bind, Except.bind] at hr
            have hc : ∀ digit ∈ digits (first :: second :: rest), Ranked (child digit) := by
              intro digit hd
              have hm : digit ∈ List.range 16 ∧ TrieBitmap.groupActive (first :: second :: rest) digit = true := by
                simpa only [digits, List.mem_filter] using hd
              exact ih _ _ (hchild digit hm.1 hm.2)
            cases hv : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd with
            | none =>
              simp only [hv] at hr
              apply Ranked.branch (first :: second :: rest) child none built hc
              simpa only [branchHeader, branchObjects, usage, digits, List.nil_append, Nat.add_zero] using hr
            | some value =>
              simp only [hv] at hr
              apply Ranked.branch (first :: second :: rest) child (some value) built hc
              simpa only [branchHeader, branchObjects, usage, digits, List.singleton_append,
                Nat.add_assoc] using hr

/-- Every nonempty certified subtree has its actual root-node rank binding. -/
theorem ranked_root_binding (built : Built) (hc : Ranked built) (hne : built.witness ≠ []) :
    NodeBinding built.witness built.root built.memoryUsage := by
  cases hc with
  | empty => exact False.elim (hne rfl)
  | leaf path value built hf =>
    have ht := finish_nodeBinding _ _ _ _ hf
    rw [ht.2]
    exact ht.1
  | extension path child built hc hf =>
    have ht := finish_nodeBinding _ _ _ _ hf
    rw [ht.2]
    exact ht.1
  | branch entries child value built hc hf =>
    have ht := finish_nodeBinding _ _ _ _ hf
    rw [ht.2]
    exact ht.1

/-- Actual finish keeps all child/value objects after the new parent node. -/
theorem finish_objects_subset (header : Bytes) (usage : Nat) (objects : Witness) (built : Built)
    (hf : finish header usage objects = .ok built) : ∀ pair ∈ objects, pair ∈ built.witness := by
  unfold finish at hf
  unfold_finish
  split at hf
  · cases hf
  · simp only [pure, Except.pure, Except.ok.injEq] at hf
    subst built
    exact fun pair hm => List.mem_cons_of_mem _ hm

/-- Node occurrences follow the certificate's node tree, rather than ranging
over all objects that happen to parse as nodes. Root occurrence is available
only for a nonempty certified subtree; edges retain actual finish equations. -/
inductive NodeOccurs : Built → Hash → Nat → Prop where
  | root (built : Built) (hc : Ranked built) (hne : built.witness ≠ []) :
      NodeOccurs built built.root built.memoryUsage
  | extension (path : List Nat) (child built : Built) (hc : Ranked child)
      (hf : finish ([3] ++ vectorBytes (encodePath false path) ++ child.root)
        (50 + 2 * (encodePath false path).length + child.memoryUsage) child.witness = .ok built)
      (root : Hash) (rank : Nat) (hn : NodeOccurs child root rank) : NodeOccurs built root rank
  | branch (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) (built : Built)
      (hc : ∀ digit ∈ digits entries, Ranked (child digit))
      (hf : finish (branchHeader entries child value) (usage entries child value)
        (branchObjects entries child value) = .ok built)
      (digit : Nat) (ha : digit ∈ digits entries)
      (root : Hash) (rank : Nat) (hn : NodeOccurs (child digit) root rank) : NodeOccurs built root rank

/-- Every recursively occurring node has an actual object binding and a rank
bounded by its subtree's usage. Each edge's positive overhead proves descent. -/
theorem nodeOccurs_binding_bound (built : Built) (root : Hash) (rank : Nat)
    (hn : NodeOccurs built root rank) :
    NodeBinding built.witness root rank ∧ rank ≤ built.memoryUsage := by
  induction hn with
  | root built hc hne => exact ⟨ranked_root_binding built hc hne, Nat.le_refl _⟩
  | extension path child built hc hf root rank hn ih =>
    have hp := finish_nodeBinding _ _ _ _ hf
    refine ⟨nodeBinding_mono _ _ _ _ (finish_objects_subset _ _ _ _ hf) ih.1, ?_⟩
    rw [hp.2]
    omega
  | branch entries child value built hc hf digit ha root rank hn ih =>
    have hp := finish_nodeBinding _ _ _ _ hf
    have hsub : ∀ pair ∈ (child digit).witness, pair ∈ branchObjects entries child value := by
      intro pair hm
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨digit, ha, hm⟩
    refine ⟨nodeBinding_mono _ _ _ _ (fun pair hm => finish_objects_subset _ _ _ _ hf pair (hsub pair hm)) ih.1, ?_⟩
    rw [hp.2]
    have ht := branch_child_usage_lt entries child value digit ha
    omega

/-- The actual public builder has a recursively certified raw node tree.
Its separate collision checker then supplies consistent merged bindings. -/
theorem build_ranked_raw (entries : List (Bytes × Bytes)) (built : Built)
    (hb : build entries = .ok built) :
    ∃ raw, construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧ Ranked raw ∧
      TrieConstructionInvariant.checkObjects raw.witness [] = .ok built.witness ∧
      built.root = raw.root ∧ built.memoryUsage = raw.memoryUsage := by
  obtain ⟨raw, hc, hr, hroot, hu⟩ := TrieConstructionInvariant.build_checked entries built hb
  exact ⟨raw, hc, construct_ranked _ _ _ hc, hr, hroot, hu⟩

/-- Any node in the certified subtree avoids all larger ranked ancestors in
a consistent containing witness. This is the node-only replacement for
excluding every hash of the entire child object list. -/
theorem nodeOccurs_ancestors_exclude (built : Built) (root : Hash) (rank : Nat)
    (hn : NodeOccurs built root rank) (target : Witness) (ancestors : List Hash)
    (hsub : ∀ pair ∈ built.witness, pair ∈ target)
    (hc : TrieWitnessTransfer.Consistent target)
    (ha : RankedAncestors target ancestors built.memoryUsage) : root ∉ ancestors := by
  have ht := nodeOccurs_binding_bound built root rank hn
  apply ranked_ancestors_exclude target hc ancestors root rank
  · intro ancestor hm
    obtain ⟨parentRank, hp, hlt⟩ := ha ancestor hm
    exact ⟨parentRank, hp, Nat.lt_of_le_of_lt ht.2 hlt⟩
  · exact nodeBinding_mono _ _ _ _ hsub ht.1

/-- Collision checking preserves the certificate's node bindings and usage
bounds in the final deduplicated witness. -/
theorem checked_nodeOccurs_binding_bound (raw built : Built) (root : Hash) (rank : Nat)
    (hn : NodeOccurs raw root rank)
    (hcheck : TrieConstructionInvariant.checkObjects raw.witness [] = .ok built.witness)
    (hu : built.memoryUsage = raw.memoryUsage) :
    NodeBinding built.witness root rank ∧ rank ≤ built.memoryUsage := by
  have ht := nodeOccurs_binding_bound raw root rank hn
  have hc := TrieConstructionInvariant.checkObjects_ok raw.witness [] built.witness
    (by intro _ _ _ h; cases h) hcheck
  refine ⟨nodeBinding_mono _ _ _ _ ?_ ht.1, ?_⟩
  · simpa only [List.nil_append] using hc.2
  · simpa only [hu] using ht.2

end Near.TrieConstructionRanks
