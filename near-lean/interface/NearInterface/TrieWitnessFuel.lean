import NearInterface.TrieConstructionInvariant

/-!
# Traversal fuel after witness deduplication

The ancestor check prevents a successful path from fetching a node twice.
Counting target records whose hashes are not ancestors gives a decreasing
measure even when witnesses contain duplicate hashes or arbitrary value
objects. No hash injectivity or nonzero-root assumption is introduced.
-/
namespace Near.TrieWitnessFuel
open TrieAccounting TrieLeaf TrieWitnessTransfer

local macro "unfold_trie_reader" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- Records whose hash has not yet occurred on the traversal path. -/
def remaining (witness : Witness) (ancestors : List Hash) : Nat :=
  (witness.filter fun pair => !ancestors.contains pair.1).length

private theorem filter_length_le (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, q x = true → p x = true) :
    (xs.filter q).length ≤ (xs.filter p).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

private theorem filter_length_lt (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, q x = true → p x = true)
    (hw : ∃ x ∈ xs, p x = true ∧ q x = false) :
    (xs.filter q).length < (xs.filter p).length := by
  induction xs with
  | nil => simp at hw
  | cons x xs ih =>
    obtain ⟨y, hy, hp, hq⟩ := hw
    have ht : ∀ z ∈ xs, q z = true → p z = true := fun z hz => h z (List.mem_cons_of_mem _ hz)
    rcases List.mem_cons.mp hy with he | hy
    · subst y
      have hl := filter_length_le xs p q ht
      simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have hl := ih ht ⟨y, hy, hp, hq⟩
      have hx := h x List.mem_cons_self
      cases hp' : p x <;> cases hq' : q x <;> simp_all <;> omega

/-- Fetching a fresh node consumes at least one remaining target record.
Duplicates strengthen the decrease rather than invalidate it. -/
theorem remaining_decreases (witness : Witness) (ancestors : List Hash) (root : Hash)
    (hroot : root ∉ ancestors) (hm : root ∈ witness.map Prod.fst) :
    remaining witness (root :: ancestors) < remaining witness ancestors := by
  apply filter_length_lt
  · intro pair _ h
    have hp : pair.1 ∉ root :: ancestors := by simpa using h
    have ha : pair.1 ∉ ancestors := fun hm => hp (List.mem_cons_of_mem _ hm)
    simpa using ha
  · obtain ⟨pair, hp, he⟩ := List.mem_map.mp hm
    refine ⟨pair, hp, ?_, ?_⟩
    · simp [he, hroot]
    · simp [he]

/-- Any successful source traversal transfers with target fuel strictly larger
than its remaining record support. Successful fetches, and the reader's own
ancestor rejection, supply every decrease needed by recursion. -/
theorem walk_transfer_bounded (source target : Witness) (hfetches : FetchRefines source target)
    (accountNodes : Bool) (fuel targetFuel : Nat) (ancestors : List Hash) (root : Hash)
    (key : List Nat) (state after : Accounting) (reference : Option ValueRef)
    (hroom : remaining target ancestors < targetFuel)
    (hwalk : walkObjects source accountNodes fuel ancestors root key state = .ok (reference, after)) :
    walkObjects target accountNodes targetFuel ancestors root key state = .ok (reference, after) := by
  induction fuel generalizing targetFuel ancestors root key state after reference with
  | zero =>
    unfold walkObjects at hwalk
    unfold_trie_reader walk
    cases hwalk
  | succ fuel ih =>
    cases targetFuel with
    | zero => omega
    | succ targetFuel =>
      unfold walkObjects at hwalk ⊢
      unfold_trie_reader walk
      by_cases hz : root == List.replicate 32 0
      · simp only [hz, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hwalk ⊢
        exact hwalk
      · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hwalk ⊢
        cases hc : ancestors.contains root with
        | true =>
          simp only [hc, ↓reduceIte] at hwalk
          cases hwalk
        | false =>
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hwalk ⊢
          cases hf : fetchObject source root with
          | error error =>
            unfold fetchObject at hf
            simp [hf, bind, Except.bind] at hwalk
          | ok bytes =>
            have htarget := hfetches root bytes hf
            have hm := fetch_mem target root bytes htarget
            have hdecrease := remaining_decreases target ancestors root (by simpa using hc)
              (List.mem_map.mpr ⟨(root, bytes), hm, rfl⟩)
            have hnext : remaining target (root :: ancestors) < targetFuel := by omega
            unfold fetchObject at hf htarget
            simp only [hf, bind, Except.bind] at hwalk
            simp only [htarget, bind, Except.bind]
            cases hd : decodeNode bytes with
            | error error => simp [hd] at hwalk
            | ok node =>
              simp only [hd] at hwalk ⊢
              cases node with
              | leaf path value => exact hwalk
              | extension path child =>
                cases hp : path.isPrefixOf key with
                | false =>
                  simp only [hp, Bool.false_eq_true, ↓reduceIte] at hwalk ⊢
                  exact hwalk
                | true =>
                  simp only [hp, ↓reduceIte] at hwalk ⊢
                  exact ih targetFuel (root :: ancestors) child (key.drop path.length) _ after reference hnext hwalk
              | branch value children =>
                cases key with
                | nil => exact hwalk
                | cons digit rest =>
                  cases hs : children.find? (·.1 == digit) with
                  | none => simp only [hs] at hwalk ⊢; exact hwalk
                  | some pair =>
                    obtain ⟨selected, child⟩ := pair
                    simp only [hs] at hwalk ⊢
                    exact ih targetFuel (root :: ancestors) child rest _ after reference hnext hwalk

/-- Default target fuel suffices for any successful source traversal started
with no ancestors, independently of how large the source witness was. -/
theorem walk_transfer_default (source target : Witness) (hfetches : FetchRefines source target)
    (accountNodes : Bool) (fuel : Nat) (root : Hash) (key : List Nat)
    (state after : Accounting) (reference : Option ValueRef)
    (hwalk : walkObjects source accountNodes fuel [] root key state = .ok (reference, after)) :
    walkObjects target accountNodes (target.length + 1) [] root key state = .ok (reference, after) := by
  apply walk_transfer_bounded source target hfetches accountNodes fuel (target.length + 1) []
    root key state after reference _ hwalk
  have hl := List.length_filter_le (fun pair : Hash × Bytes => !([] : List Hash).contains pair.1) target
  change (target.filter _).length < target.length + 1
  omega

/-- Successful value fetching is preserved along the same binding refinement. -/
theorem dereference_transfer (source target : Witness) (hfetches : FetchRefines source target)
    (reference : ValueRef) (state after : Accounting) (value : Bytes)
    (hd : dereference source reference state = .ok (value, after)) :
    dereference target reference state = .ok (value, after) := by
  cases hf : fetchObject source reference.hash with
  | error error =>
    unfold fetchObject at hf
    simp [dereference, hf, bind, Except.bind] at hd
  | ok bytes =>
    have ht := hfetches reference.hash bytes hf
    unfold fetchObject at hf ht
    simpa only [dereference, hf, ht, bind, Except.bind] using hd

/-- Complete actual lookup, including optional value dereference and its
accounting, survives arbitrary witness compaction that preserves bindings.
The target uses its own possibly smaller default traversal fuel. -/
theorem lookup_transfer (source target : Witness) (hfetches : FetchRefines source target)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hr : lookup source root previous query = .ok result) :
    lookup target root previous query = .ok result := by
  cases hw : walkObjects source query.accountNodes (source.length + 1) [] root (nibbles query.key)
      (queryStart previous query) with
  | error error =>
    unfold walkObjects queryStart at hw
    simp only [lookup, hw, bind, Except.bind] at hr
    cases hr
  | ok pair =>
    obtain ⟨reference, state⟩ := pair
    have ht := walk_transfer_default source target hfetches query.accountNodes (source.length + 1)
      root (nibbles query.key) (queryStart previous query) state reference hw
    unfold walkObjects queryStart at hw ht
    simp only [lookup, hw, ht, bind, Except.bind] at hr ⊢
    cases reference with
    | none => exact hr
    | some reference =>
      cases hm : query.dereference with
      | false => simpa only [hm, Bool.false_eq_true, ↓reduceIte] using hr
      | true =>
        simp only [hm, ↓reduceIte] at hr ⊢
        cases hd : dereference source reference state with
        | error error => simp [hd] at hr
        | ok pair =>
          obtain ⟨value, after⟩ := pair
          have hdt := dereference_transfer source target hfetches reference state after value hd
          simpa only [hd, hdt, bind, Except.bind] using hr

/-- The actual successful public build preserves every successful lookup of
its raw recursive construction despite deduplication reducing default fuel. -/
theorem build_lookup_transfer (entries : List (Bytes × Bytes)) (built raw : TrieConstruction.Built)
    (hbuild : TrieConstruction.build entries = .ok built)
    (hconstruct : TrieConstructionBranch.construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw)
    (previous : Accounting) (query : Query) (result : Result)
    (hr : lookup raw.witness raw.root previous query = .ok result) :
    lookup built.witness built.root previous query = .ok result := by
  obtain ⟨other, hc, _, hroot, _⟩ := TrieConstructionInvariant.build_checked entries built hbuild
  rw [hconstruct] at hc
  cases Except.ok.inj hc
  rw [hroot]
  exact lookup_transfer raw.witness built.witness
    (TrieConstructionInvariant.build_raw_checked entries built raw hbuild hconstruct).2.2
    raw.root previous query result hr

end Near.TrieWitnessFuel
