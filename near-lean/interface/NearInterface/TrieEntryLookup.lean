import NearInterface.TrieReadableConstruction

/-! First-match raw entry semantics for actual trie construction. -/
namespace Near.TrieEntryLookup
open TrieAccounting TrieConstruction TrieSerialization TrieConstructionBranch
open TrieBranchConstructionLookup TrieConstructionRanks TrieRankedLookup TrieReadableConstruction

local macro "unfold_construct" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "construct"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- Independent first-match lookup of a nibble key in the input entry list. -/
def entryValue : List (List Nat × Bytes) → List Nat → Option Bytes
  | [], _ => none
  | (path, value) :: rest, key => if path == key then some value else entryValue rest key

def referenceOf (value : Bytes) : ValueRef := { length := value.length, hash := Sha256.hash value }
def entryReference (entries : List (List Nat × Bytes)) (key : List Nat) : Option ValueRef :=
  (entryValue entries key).map referenceOf

theorem entryValue_find (entries : List (List Nat × Bytes)) (key : List Nat) :
    entryValue entries key = (entries.find? (fun entry => entry.1 == key)).map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨path, value⟩ := entry
    by_cases he : path = key <;> simp [entryValue, ih, he]

theorem entryValue_mem (entries : List (List Nat × Bytes)) (key : List Nat) (value : Bytes)
    (hv : entryValue entries key = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => cases hv
  | cons entry entries ih =>
    obtain ⟨path, before⟩ := entry
    simp only [entryValue] at hv
    split at hv
    · rename_i he
      have hp : path = key := by simpa using he
      subst path
      cases Option.some.inj hv
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hv)

/-- The actual common-front helper retains a front of both arguments. -/
theorem commonPath_front (left right : List Nat) : commonPath left right <+: left ∧ commonPath left right <+: right := by
  induction left generalizing right with
  | nil => change [] <+: [] ∧ [] <+: right; simp
  | cons a left ih =>
    cases right with
    | nil => change [] <+: (a :: left) ∧ [] <+: []; simp
    | cons b right =>
      have he : commonPath (a :: left) (b :: right) = if a == b then a :: commonPath left right else [] := rfl
      rw [he]
      by_cases hab : a = b
      · subst b
        simpa only [beq_self_eq_true, ↓reduceIte, List.cons_prefix_cons, true_and] using ih right
      · simp [hab]

theorem sharedPath_front (entries : List (List Nat × Bytes)) (path : List Nat) :
    let shared := entries.foldl (fun path entry => commonPath path entry.1) path
    shared <+: path ∧ ∀ entry ∈ entries, shared <+: entry.1 := by
  induction entries generalizing path with
  | nil => exact ⟨by simp, by simp⟩
  | cons entry entries ih =>
    have ht := ih (commonPath path entry.1)
    have hp := commonPath_front path entry.1
    refine ⟨ht.1.trans hp.1, ?_⟩
    intro next hm
    rcases List.mem_cons.mp hm with he | hm
    · subst next; exact ht.1.trans hp.2
    · exact ht.2 next hm

/-- Dropping one common front preserves key equality exactly. -/
theorem drop_eq_iff (front first second : List Nat) (hf : front <+: first) (hs : front <+: second) :
    first.drop front.length = second.drop front.length ↔ first = second := by
  constructor
  · intro hd
    have hfirst := List.prefix_iff_eq_append.mp hf
    have hsecond := List.prefix_iff_eq_append.mp hs
    rw [hd] at hfirst
    exact hfirst.symm.trans hsecond
  · intro he; rw [he]

theorem entryValue_drop (entries : List (List Nat × Bytes)) (front key : List Nat)
    (hp : ∀ entry ∈ entries, front <+: entry.1) (hk : front <+: key) :
    entryValue (entries.map fun (path, value) => (path.drop front.length, value)) (key.drop front.length) =
      entryValue entries key := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨path, value⟩ := entry
    have he : (path.drop front.length == key.drop front.length) = (path == key) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [beq_iff_eq] using drop_eq_iff front path key (hp _ List.mem_cons_self) hk
    simp only [List.map_cons, entryValue, he]
    split
    · rfl
    · exact ih (fun entry hm => hp entry (List.mem_cons_of_mem _ hm))

theorem entryValue_front_miss (entries : List (List Nat × Bytes)) (front key : List Nat)
    (hp : ∀ entry ∈ entries, front <+: entry.1) (hk : front.isPrefixOf key = false) :
    entryValue entries key = none := by
  cases hv : entryValue entries key with
  | none => rfl
  | some value =>
    have hm := entryValue_mem entries key value hv
    have ht : front.isPrefixOf key = true := List.isPrefixOf_iff_prefix.mpr (hp _ hm)
    rw [hk] at ht
    cases ht

/-- Filtering by the head digit and removing it preserves first-match order. -/
theorem entryValue_group (entries : List (List Nat × Bytes)) (digit : Nat) (tail : List Nat) :
    entryValue ((entries.filter fun entry => entry.1.head? == some digit).map fun (key, value) => (key.tail, value)) tail =
      entryValue entries (digit :: tail) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨path, value⟩ := entry
    cases path with
    | nil => simpa [List.filter_cons, entryValue] using ih
    | cons head rest =>
      by_cases he : head = digit
      · subst head
        simp [entryValue, ih]
      · simp [entryValue, he, ih]

/-- Branch-terminal value selection is exactly independent empty-key lookup. -/
theorem entryValue_empty (entries : List (List Nat × Bytes)) :
    (entries.find? (fun entry => entry.1.isEmpty)).map Prod.snd = entryValue entries [] := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨path, value⟩ := entry
    cases path <;> simp [entryValue, ih]

theorem entryValue_unselected (entries : List (List Nat × Bytes)) (digit : Nat) (tail : List Nat)
    (hv : ValidEntries entries) (hn : digit ∉ digits entries) : entryValue entries (digit :: tail) = none := by
  cases he : entryValue entries (digit :: tail) with
  | none => rfl
  | some value =>
    have hm := entryValue_mem entries (digit :: tail) value he
    have hd : digit < 16 := (hv _ hm).1 digit List.mem_cons_self
    have hg : (digit :: tail, value) ∈ entries.filter (fun entry => entry.1.head? == some digit) := by simp [hm]
    have ha : TrieBitmap.groupActive entries digit = true := by
      unfold TrieBitmap.groupActive
      cases hf : entries.filter (fun entry => entry.1.head? == some digit) with
      | nil => rw [hf] at hg; cases hg
      | cons first rest => rfl
    exact False.elim (hn (by simp [digits, hd, ha]))

/-- A branch's pure answer is first-match entry lookup whenever its recursively
constructed children answer their actual head-digit groups. -/
theorem ofBranch_answers (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (built : Built) (trees : ∀ digit ∈ digits entries, Tree (child digit))
    (hf : finish (branchHeader entries child value) (usage entries child value)
      (branchObjects entries child value) = .ok built)
    (hv : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32)
    (hvalid : ValidEntries entries)
    (hvalue : (entries.find? (fun entry => entry.1.isEmpty)).map Prod.snd = value)
    (hanswers : ∀ digit hd key, (trees digit hd).answer key = entryReference
      ((entries.filter fun entry => entry.1.head? == some digit).map fun (key, value) => (key.tail, value)) key) :
    ∀ key, (Tree.ofBranch entries child value built trees hf hv).answer key = entryReference entries key := by
  intro key
  cases key with
  | nil =>
    change valueReference value = (entryValue entries []).map referenceOf
    rw [← entryValue_empty entries, hvalue]
    rfl
  | cons digit rest =>
    by_cases hm : digit ∈ digits entries
    · simp only [Tree.ofBranch, Tree.answer, hm, ↓reduceDIte]
      rw [hanswers digit hm rest]
      unfold entryReference
      rw [entryValue_group]
    · simp only [Tree.ofBranch, Tree.answer, hm, ↓reduceDIte]
      unfold entryReference
      rw [entryValue_unselected entries digit rest hvalid hm]
      rfl

/-- Actual recursive construction supplies a tree whose pure answers equal
independent first-match lookup, for every nibble query. No uniqueness premise
is needed: the constructor and the specification both retain first matches. -/
theorem construct_answers (fuel : Nat) (entries : List (List Nat × Bytes)) (built : Built)
    (hv : ValidEntries entries) (hr : construct fuel entries = .ok built) : ∃ tree : Tree built, ∀ key, tree.answer key = entryReference entries key := by
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
      exact ⟨.empty, by intro key; rfl⟩
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
        · refine ⟨Tree.ofLeaf path value built hr (hv _ List.mem_cons_self).1
            (by omega) (hv _ List.mem_cons_self).2, ?_⟩
          intro key
          simp only [Tree.ofLeaf, Tree.answer, entryReference, entryValue]
          split <;> rfl
      | cons second rest =>
        rw [construct_many] at hr
        dsimp only at hr
        split at hr
        · rename_i hshared
          cases hc : construct fuel ((first :: second :: rest).map fun (key, value) =>
              (key.drop ((second :: rest).foldl (fun path entry => commonPath path entry.1) first.1).length, value)) with
          | error error => simp only [hc, bind, Except.bind] at hr; cases hr
          | ok child =>
            simp only [hc, bind, Except.bind] at hr
            split at hr
            · change Except.error _ = Except.ok _ at hr; cases hr
            · obtain ⟨tree, hanswer⟩ := ih _ child (dropped_valid _ _ hv) hc
              have hpath := sharedPath_valid (second :: rest) first.1 (hv first List.mem_cons_self).1
              have hn : (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 ≠ [] := by
                intro he
                simp only [he, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at hshared
              refine ⟨Tree.ofExtension _ child built tree hr hpath hn (by omega), ?_⟩
              intro key
              have hp := sharedPath_front (second :: rest) first.1
              have hall : ∀ entry ∈ first :: second :: rest,
                  (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 <+: entry.1 := by
                intro entry hm
                rcases List.mem_cons.mp hm with he | hm
                · subst entry; exact hp.1
                · exact hp.2 entry hm
              cases hk : ((second :: rest).foldl (fun path entry => commonPath path entry.1) first.1).isPrefixOf key with
              | false =>
                simp only [Tree.ofExtension, Tree.answer, hk, Bool.false_eq_true, ↓reduceIte]
                unfold entryReference
                rw [entryValue_front_miss _ _ key hall hk]
                rfl
              | true =>
                simp only [Tree.ofExtension, Tree.answer, hk, ↓reduceIte]
                rw [hanswer]
                unfold entryReference
                rw [entryValue_drop _ _ key hall (List.isPrefixOf_iff_prefix.mp hk)]
        · cases hl : branchLoop fuel (first :: second :: rest) with
          | error error => simp only [hl, bind, Except.bind] at hr; cases hr
          | ok acc =>
            obtain ⟨child, hchild⟩ := branchLoop_children fuel (first :: second :: rest) acc hl
            have he := branchLoop_contract fuel (first :: second :: rest) child hchild
            rw [hl] at he
            have heq := Except.ok.inj he
            subst acc
            simp only [hl, bind, Except.bind] at hr
            have hc : ∀ digit ∈ digits (first :: second :: rest), ∃ tree : Tree (child digit), ∀ key,
                tree.answer key = entryReference
                  (((first :: second :: rest).filter fun entry => entry.1.head? == some digit).map fun (key, value) => (key.tail, value)) key := by
              intro digit hd
              have hm : digit ∈ List.range 16 ∧ TrieBitmap.groupActive (first :: second :: rest) digit = true := by
                simpa only [digits, List.mem_filter] using hd
              exact ih _ _ (group_valid _ digit hv) (hchild digit hm.1 hm.2)
            let trees := fun digit hd => Classical.choose (hc digit hd)
            have hanswers := fun digit hd => Classical.choose_spec (hc digit hd)
            cases hval : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd with
            | none =>
              simp only [hval] at hr
              have hf : finish (branchHeader (first :: second :: rest) child none)
                  (usage (first :: second :: rest) child none)
                  (branchObjects (first :: second :: rest) child none) = .ok built := by
                simpa only [branchHeader, branchObjects, usage, digits, List.nil_append, Nat.add_zero] using hr
              have hvalue : ∀ bytes, (none : Option Bytes) = some bytes → bytes.length < 2 ^ 32 := by
                intro bytes he; cases he
              exact ⟨Tree.ofBranch _ child none built trees hf hvalue,
                ofBranch_answers _ child none built trees hf hvalue hv hval hanswers⟩
            | some value =>
              simp only [hval] at hr
              have hf : finish (branchHeader (first :: second :: rest) child (some value))
                  (usage (first :: second :: rest) child (some value))
                  (branchObjects (first :: second :: rest) child (some value)) = .ok built := by
                simpa only [branchHeader, branchObjects, usage, digits, List.singleton_append, Nat.add_assoc] using hr
              have hvalue : ∀ bytes, some value = some bytes → bytes.length < 2 ^ 32 := by
                intro bytes he
                cases Option.some.inj he
                cases hf : (first :: second :: rest).find? (fun entry => entry.1.isEmpty) with
                | none => simp [hf] at hval
                | some entry =>
                  have hm := List.mem_of_find?_eq_some hf
                  simp only [hf, Option.map_some, Option.some.injEq] at hval
                  simpa only [hval] using (hv entry hm).2
              exact ⟨Tree.ofBranch _ child (some value) built trees hf hvalue,
                ofBranch_answers _ child (some value) built trees hf hvalue hv hval hanswers⟩


/-- A root produced by finish is a genuine node occurrence: its object list
cannot be empty. -/
private theorem finish_nonempty (header : Bytes) (usage : Nat) (objects : Witness) (built : Built)
    (hf : finish header usage objects = .ok built) : built.witness ≠ [] := by
  obtain ⟨_, hm, _⟩ := (TrieNodeRank.finish_nodeBinding header usage objects built hf).1
  exact List.ne_nil_of_mem hm

/-- Node-only reserved-zero exclusion implies the traversal certificate's
explicit nonzero condition. No arbitrary value-object hash is constrained. -/
theorem tree_nonzero_of_occurs {built : Built} (tree : Tree built)
    (hz : ∀ root rank, NodeOccurs built root rank → root ≠ List.replicate 32 0) : tree.Nonzero := by
  induction tree with
  | empty => trivial
  | leaf path value built hf hd =>
    exact hz built.root built.memoryUsage (.root built (.leaf path value built hf) (finish_nonempty _ _ _ _ hf))
  | extension path child built tree hf hd ih =>
    refine ⟨hz built.root built.memoryUsage (.root built (.extension path child built tree.ranked hf)
      (finish_nonempty _ _ _ _ hf)), ?_⟩
    exact ih (fun root rank hn => hz root rank (.extension path child built tree.ranked hf root rank hn))
  | branch entries child value built trees hf hd ih =>
    have hc : ∀ digit hd, Ranked (child digit) := fun digit hd => (trees digit hd).ranked
    refine ⟨hz built.root built.memoryUsage (.root built (.branch entries child value built hc hf)
      (finish_nonempty _ _ _ _ hf)), ?_⟩
    intro digit hm
    exact ih digit hm (fun root rank hn => hz root rank (.branch entries child value built hc hf digit hm root rank hn))

/-- Actual reference-only lookup of the public deduplicated trie equals
independent first-match input lookup. Only the reserved-zero-node issue is
left explicit; serialization, recursion, alias consistency and fuel are proved. -/
theorem build_reference_entries (entries : List (Bytes × Bytes)) (built raw : Built)
    (hb : build entries = .ok built)
    (hc : construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw)
    (hz : ∀ root rank, NodeOccurs raw root rank → root ≠ List.replicate 32 0)
    (previous : Accounting) (query : Query) (hmode : query.dereference = false) :
    ∃ after, lookup built.witness built.root previous query = .ok {
      reference := entryReference (entries.map fun (key, value) => (nibbles key, value)) (nibbles query.key),
      value := none, state := after } := by
  obtain ⟨tree, hanswer⟩ := construct_answers _ _ raw (build_inputs_valid entries built hb) hc
  obtain ⟨after, hr⟩ := build_lookup_answer_reference entries built raw hb hc tree
    (tree_nonzero_of_occurs tree hz) previous query hmode
  exact ⟨after, by simpa only [hanswer] using hr⟩

/-- Public build exposes the actual raw result for which the only remaining
lookup premise is nonzero hashes of certified node occurrences. -/
theorem build_reference_entries_exists (entries : List (Bytes × Bytes)) (built : Built)
    (hb : build entries = .ok built) :
    ∃ raw, construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧
      ∀ previous query, query.dereference = false →
        (∀ root rank, NodeOccurs raw root rank → root ≠ List.replicate 32 0) →
        ∃ after, lookup built.witness built.root previous query = .ok {
          reference := entryReference (entries.map fun (key, value) => (nibbles key, value)) (nibbles query.key),
          value := none, state := after } := by
  obtain ⟨raw, hc, _, _, _⟩ := TrieConstructionInvariant.build_checked entries built hb
  exact ⟨raw, hc, fun previous query hm hz => build_reference_entries entries built raw hb hc hz previous query hm⟩

/-- Byte keys cannot collide under the actual two-nibble expansion. -/
theorem nibbles_injective (left right : Bytes) (he : nibbles left = nibbles right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons b rest => simp [nibbles] at he
  | cons a left ih =>
    cases right with
    | nil => simp [nibbles] at he
    | cons b right =>
      change a.toNat / 16 :: a.toNat % 16 :: nibbles left =
        b.toNat / 16 :: b.toNat % 16 :: nibbles right at he
      obtain ⟨hdiv, hrest⟩ := List.cons.inj he
      obtain ⟨hmod, htail⟩ := List.cons.inj hrest
      have hab : a = b := UInt8.toNat_inj.mp (by omega)
      subst b
      exact congrArg (List.cons a) (ih right htail)

theorem entryValue_nibbles (entries : List (Bytes × Bytes)) (key : Bytes) :
    entryValue (entries.map fun (path, value) => (nibbles path, value)) (nibbles key) =
      (entries.find? (fun entry => entry.1 == key)).map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨path, value⟩ := entry
    by_cases he : path = key
    · subst path
      simp [entryValue]
    · have hn : nibbles path ≠ nibbles key := fun h => he (nibbles_injective path key h)
      simpa [entryValue, he, hn] using ih

/-- Actual final reference-only lookup expressed directly on original byte
keys and first-match byte values, without an intermediate tree or nibble map. -/
theorem build_reference_bytes (entries : List (Bytes × Bytes)) (built raw : Built)
    (hb : build entries = .ok built)
    (hc : construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw)
    (hz : ∀ root rank, NodeOccurs raw root rank → root ≠ List.replicate 32 0)
    (previous : Accounting) (query : Query) (hmode : query.dereference = false) :
    ∃ after, lookup built.witness built.root previous query = .ok {
      reference := (entries.find? (fun entry => entry.1 == query.key)).map (fun entry => referenceOf entry.2),
      value := none, state := after } := by
  obtain ⟨after, hr⟩ := build_reference_entries entries built raw hb hc hz previous query hmode
  refine ⟨after, ?_⟩
  simpa only [entryReference, entryValue_nibbles, Option.map_map, Function.comp_def] using hr

end Near.TrieEntryLookup
