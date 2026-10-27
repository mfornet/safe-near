import NearInterface.TrieRankedLookup

/-! Actual successful construction produces locally decoded tree certificates.
Input nibbles and value widths are propagated through the real recursive
transformations. Node nonzero conditions remain separate. -/
namespace Near.TrieReadableConstruction
open TrieAccounting TrieConstruction TrieSerialization TrieConstructionBranch
open TrieBranchConstructionLookup TrieConstructionRanks TrieRankedLookup

local macro "unfold_construct" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "construct"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- Serialization-relevant input invariant; no uniqueness assumption is needed
for readability alone. Public build independently rejects duplicate keys. -/
def ValidEntries (entries : List (List Nat × Bytes)) : Prop :=
  ∀ entry ∈ entries, ValidPath entry.1 ∧ entry.2.length < 2 ^ 32

theorem validPath_drop (path : List Nat) (count : Nat) (hv : ValidPath path) : ValidPath (path.drop count) :=
  fun n hn => hv n (List.mem_of_mem_drop hn)

theorem validPath_tail (path : List Nat) (hv : ValidPath path) : ValidPath path.tail :=
  fun n hn => hv n (List.mem_of_mem_tail hn)

/-- Common prefixes contain only digits from the first path. -/
theorem commonPath_valid (left right : List Nat) (hv : ValidPath left) : ValidPath (commonPath left right) := by
  induction left generalizing right with
  | nil => cases right <;> exact (by intro n hn; cases hn)
  | cons a left ih =>
    cases right with
    | nil => exact (by intro n hn; cases hn)
    | cons b right =>
      have he : commonPath (a :: left) (b :: right) =
          if a == b then a :: commonPath left right else [] := rfl
      rw [he]
      split
      · intro n hn
        rcases List.mem_cons.mp hn with he | hn
        · subst n; exact hv a List.mem_cons_self
        · exact ih right (fun n hn => hv n (List.mem_cons_of_mem _ hn)) n hn
      · intro n hn; cases hn

theorem sharedPath_valid (entries : List (List Nat × Bytes)) (path : List Nat) (hv : ValidPath path) :
    ValidPath (entries.foldl (fun path entry => commonPath path entry.1) path) := by
  induction entries generalizing path with
  | nil => exact hv
  | cons entry entries ih => exact ih _ (commonPath_valid path entry.1 hv)

theorem dropped_valid (entries : List (List Nat × Bytes)) (count : Nat) (hv : ValidEntries entries) :
    ValidEntries (entries.map fun (key, value) => (key.drop count, value)) := by
  intro entry hm
  obtain ⟨⟨path, value⟩, hp, he⟩ := List.mem_map.mp hm
  subst entry
  exact ⟨validPath_drop path count (hv _ hp).1, (hv _ hp).2⟩

theorem group_valid (entries : List (List Nat × Bytes)) (digit : Nat) (hv : ValidEntries entries) :
    ValidEntries ((entries.filter fun entry => entry.1.head? == some digit).map fun (key, value) => (key.tail, value)) := by
  intro entry hm
  obtain ⟨⟨path, value⟩, hp, he⟩ := List.mem_map.mp hm
  subst entry
  have ht := hv (path, value) (List.mem_filter.mp hp).1
  exact ⟨validPath_tail path ht.1, ht.2⟩

/-- The actual recursive constructor supplies every local serialization guard,
so valid input paths/values yield a real decoded tree, not merely a rank tree. -/
theorem construct_readable (fuel : Nat) (entries : List (List Nat × Bytes)) (built : Built)
    (hv : ValidEntries entries) (hr : construct fuel entries = .ok built) : Nonempty (Tree built) := by
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
      exact ⟨.empty⟩
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
        · exact ⟨Tree.ofLeaf path value built hr (hv _ List.mem_cons_self).1
            (by omega) (hv _ List.mem_cons_self).2⟩
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
            · obtain ⟨tree⟩ := ih _ child (dropped_valid _ _ hv) hc
              refine ⟨Tree.ofExtension _ child built tree hr ?_ ?_ (by omega)⟩
              · exact sharedPath_valid (second :: rest) first.1 (hv first List.mem_cons_self).1
              · intro he
                simp only [he, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at hshared
        · cases hl : branchLoop fuel (first :: second :: rest) with
          | error error => simp only [hl, bind, Except.bind] at hr; cases hr
          | ok acc =>
            obtain ⟨child, hchild⟩ := branchLoop_children fuel (first :: second :: rest) acc hl
            have he := branchLoop_contract fuel (first :: second :: rest) child hchild
            rw [hl] at he
            have heq := Except.ok.inj he
            subst acc
            simp only [hl, bind, Except.bind] at hr
            have hc : ∀ digit ∈ digits (first :: second :: rest), Nonempty (Tree (child digit)) := by
              intro digit hd
              have hm : digit ∈ List.range 16 ∧ TrieBitmap.groupActive (first :: second :: rest) digit = true := by
                simpa only [digits, List.mem_filter] using hd
              exact ih _ _ (group_valid _ digit hv) (hchild digit hm.1 hm.2)
            let trees := fun digit hd => Classical.choice (hc digit hd)
            cases hval : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd with
            | none =>
              simp only [hval] at hr
              refine ⟨Tree.ofBranch (first :: second :: rest) child none built trees ?_ ?_⟩
              · simpa only [branchHeader, branchObjects, usage, digits, List.nil_append, Nat.add_zero] using hr
              · intro bytes he; cases he
            | some value =>
              simp only [hval] at hr
              refine ⟨Tree.ofBranch (first :: second :: rest) child (some value) built trees ?_ ?_⟩
              · simpa only [branchHeader, branchObjects, usage, digits, List.singleton_append, Nat.add_assoc] using hr
              · intro bytes he
                cases Option.some.inj he
                cases hf : (first :: second :: rest).find? (fun entry => entry.1.isEmpty) with
                | none => simp [hf] at hval
                | some entry =>
                  have hm := List.mem_of_find?_eq_some hf
                  simp only [hf, Option.map_some, Option.some.injEq] at hval
                  simpa only [hval] using (hv entry hm).2

/-- Public build's actual size guard supplies every value-u32 obligation;
its byte-to-nibble conversion supplies path validity independently of lengths. -/
theorem build_inputs_valid (entries : List (Bytes × Bytes)) (built : Built)
    (hb : build entries = .ok built) :
    ValidEntries (entries.map fun (key, value) => (nibbles key, value)) := by
  change (if (entries.map Prod.fst).eraseDups.length != (entries.map Prod.fst).length then
      .error "duplicate trie entry"
    else if entries.any (fun (key, value) => key.length ≥ 2 ^ 32 || value.length ≥ 2 ^ 32) then
      .error "trie key or value exceeds u32"
    else do
      let raw ← construct (TrieConstructionInvariant.constructionDepth entries)
        (entries.map fun (key, value) => (nibbles key, value))
      let unique ← TrieConstructionInvariant.checkObjects raw.witness []
      pure { raw with witness := unique }) = .ok built at hb
  split at hb
  · cases hb
  · split at hb
    · cases hb
    · rename_i hsize
      intro entry hm
      obtain ⟨⟨key, value⟩, hp, he⟩ := List.mem_map.mp hm
      subst entry
      refine ⟨nibbles_valid key, ?_⟩
      have hf : entries.any (fun (key, value) => key.length ≥ 2 ^ 32 || value.length ≥ 2 ^ 32) = false :=
        Bool.eq_false_iff.mpr hsize
      have ht := List.any_eq_false.mp hf (key, value) hp
      by_cases hv : value.length < 2 ^ 32
      · exact hv
      · exact False.elim (ht (by simp [Nat.le_of_not_gt hv]))

/-- A successful actual public build exposes a locally decoded recursive tree
for its raw construction result. Only nonzero-node evidence remains separate. -/
theorem build_readable_raw (entries : List (Bytes × Bytes)) (built : Built)
    (hb : build entries = .ok built) :
    ∃ raw, construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧
      Nonempty (Tree raw) ∧
      TrieConstructionInvariant.checkObjects raw.witness [] = .ok built.witness ∧
      built.root = raw.root ∧ built.memoryUsage = raw.memoryUsage := by
  obtain ⟨raw, hc, hr, hroot, hu⟩ := TrieConstructionInvariant.build_checked entries built hb
  exact ⟨raw, hc, construct_readable _ _ raw (build_inputs_valid entries built hb) hc, hr, hroot, hu⟩

/-- Public construction always supplies the local decoder certificate used by
the actual traversal theorem. Nonzero and the intended answer remain separate
from this existence result, rather than being inferred from SHA-256. -/
theorem build_reference_readable (entries : List (Bytes × Bytes)) (built : Built)
    (hb : build entries = .ok built) :
    ∃ raw, ∃ tree : Tree raw,
      construct (TrieConstructionInvariant.constructionDepth entries)
        (entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧
      ∀ previous query, query.dereference = false → tree.Nonzero →
        ∃ after, lookup built.witness built.root previous query = .ok {
          reference := tree.answer (nibbles query.key), value := none, state := after } := by
  obtain ⟨raw, hc, ⟨tree⟩, _, _, _⟩ := build_readable_raw entries built hb
  exact ⟨raw, tree, hc, fun previous query hm hz =>
    build_lookup_answer_reference entries built raw hb hc tree hz previous query hm⟩

end Near.TrieReadableConstruction
