import NearInterface.TrieLeaf
import NearInterface.TrieBranch

/-!
# Actual branch-node traversal

Both branch variants share this traversal: empty keys use the optional value,
nonempty keys select a child by first matching digit. Root-sentinel and cycle
conditions are explicit; child facts concern the actual recursive walker at
its exact remaining fuel, ancestor list, key tail and accounting state.
-/
namespace Near.TrieBranchLookup
open TrieAccounting TrieLeaf

local macro "unfold_trie_reader" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))

/-- Exact actual branch traversal, with no child-shape or uniqueness premise. -/
theorem walkObjects_branch (witness : Witness) (root : Hash) (bytes : Bytes)
    (value : Option ValueRef) (children : List (Nat × Hash)) (key : List Nat)
    (state : Accounting) (ancestors : List Hash) (accountNodes : Bool) (fuel : Nat)
    (hroot : root ≠ List.replicate 32 0) (hcycle : ancestors.contains root = false)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children)) :
    walkObjects witness accountNodes (fuel + 1) ancestors root key state =
      match key with
      | [] => .ok (value, if accountNodes then state.touch root "node" else state)
      | digit :: rest => match children.find? (fun pair : Nat × Hash => pair.1 == digit) with
        | none => .ok (none, if accountNodes then state.touch root "node" else state)
        | some (_, child) => walkObjects witness accountNodes fuel (root :: ancestors) child rest
            (if accountNodes then state.touch root "node" else state) := by
  generalize hresult : (match key with
    | [] => Except.ok (value, if accountNodes then state.touch root "node" else state)
    | digit :: rest => match children.find? (fun pair : Nat × Hash => pair.1 == digit) with
      | none => Except.ok (none, if accountNodes then state.touch root "node" else state)
      | some (_, child) => walkObjects witness accountNodes fuel (root :: ancestors) child rest
          (if accountNodes then state.touch root "node" else state)) = result
  unfold walkObjects
  unfold_trie_reader walk
  unfold fetchObject at hfetch
  simp only [beq_eq_false_iff_ne.mpr hroot, Bool.false_eq_true, ↓reduceIte,
    hcycle, bind, Except.bind, hfetch, hdecode, pure, Except.pure]
  unfold walkObjects at hresult
  exact hresult

/-- An exhausted key returns the branch's optional value and one node touch. -/
theorem walkObjects_branch_empty (witness : Witness) (root : Hash) (bytes : Bytes)
    (value : Option ValueRef) (children : List (Nat × Hash))
    (state : Accounting) (ancestors : List Hash) (accountNodes : Bool) (fuel : Nat)
    (hroot : root ≠ List.replicate 32 0) (hcycle : ancestors.contains root = false)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children)) :
    walkObjects witness accountNodes (fuel + 1) ancestors root [] state =
      .ok (value, if accountNodes then state.touch root "node" else state) := by
  rw [walkObjects_branch witness root bytes value children [] state ancestors accountNodes fuel
    hroot hcycle hfetch hdecode]

/-- The first selected child consumes one nibble and inherits the exact cache.
Both branches with and without a stored value use the same equation. -/
theorem walkObjects_branch_child (witness : Witness) (root child : Hash) (bytes : Bytes)
    (value reference : Option ValueRef) (children : List (Nat × Hash)) (digit : Nat) (rest : List Nat)
    (state after : Accounting) (ancestors : List Hash) (accountNodes : Bool) (fuel : Nat)
    (hroot : root ≠ List.replicate 32 0) (hcycle : ancestors.contains root = false)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children))
    (hselected : children.find? (fun pair : Nat × Hash => pair.1 == digit) = some (digit, child))
    (hchild : walkObjects witness accountNodes fuel (root :: ancestors) child rest
      (if accountNodes then state.touch root "node" else state) = .ok (reference, after)) :
    walkObjects witness accountNodes (fuel + 1) ancestors root (digit :: rest) state =
      .ok (reference, after) := by
  rw [walkObjects_branch witness root bytes value children (digit :: rest) state ancestors accountNodes fuel
    hroot hcycle hfetch hdecode]
  simp only [hselected]
  exact hchild

/-- A missing digit terminates before any child witness access. -/
theorem walkObjects_branch_miss (witness : Witness) (root : Hash) (bytes : Bytes)
    (value : Option ValueRef) (children : List (Nat × Hash)) (digit : Nat) (rest : List Nat)
    (state : Accounting) (ancestors : List Hash) (accountNodes : Bool) (fuel : Nat)
    (hroot : root ≠ List.replicate 32 0) (hcycle : ancestors.contains root = false)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children))
    (hselected : children.find? (fun pair : Nat × Hash => pair.1 == digit) = none) :
    walkObjects witness accountNodes (fuel + 1) ancestors root (digit :: rest) state =
      .ok (none, if accountNodes then state.touch root "node" else state) := by
  rw [walkObjects_branch witness root bytes value children (digit :: rest) state ancestors accountNodes fuel
    hroot hcycle hfetch hdecode]
  simp only [hselected]

/-- The empty key observes the optional branch reference without dereference. -/
theorem lookup_branch_empty_reference (witness : Witness) (root : Hash) (bytes : Bytes)
    (value : Option ValueRef) (children : List (Nat × Hash)) (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children))
    (hkey : nibbles query.key = []) (hmode : query.dereference = false) :
    lookup witness root previous query = .ok {
      reference := value, value := none,
      state := if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query } := by
  have hw := walkObjects_branch_empty witness root bytes value children (queryStart previous query)
    [] query.accountNodes witness.length hroot rfl hfetch hdecode
  unfold walkObjects queryStart at hw
  simp only [lookup, hkey, hw, bind, Except.bind]
  cases value <;> simp [hmode, queryStart, pure, Except.pure]

/-- Actual reference-only lookup through the selected child. -/
theorem lookup_branch_child_reference (witness : Witness) (root child : Hash) (bytes : Bytes)
    (value reference : Option ValueRef) (children : List (Nat × Hash)) (digit : Nat) (rest : List Nat)
    (previous after : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children))
    (hkey : nibbles query.key = digit :: rest)
    (hselected : children.find? (fun pair : Nat × Hash => pair.1 == digit) = some (digit, child))
    (hchild : walkObjects witness query.accountNodes witness.length [root] child rest
      (if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query) = .ok (reference, after))
    (hmode : query.dereference = false) :
    lookup witness root previous query = .ok { reference, value := none, state := after } := by
  have hw := walkObjects_branch_child witness root child bytes value reference children digit rest
    (queryStart previous query) after [] query.accountNodes witness.length hroot rfl hfetch hdecode hselected hchild
  unfold walkObjects queryStart at hw
  simp only [lookup, hkey, hw, bind, Except.bind]
  cases reference <;> simp [hmode, pure, Except.pure]

/-- A missing child gives an absent lookup regardless of dereference mode. -/
theorem lookup_branch_miss (witness : Witness) (root : Hash) (bytes : Bytes)
    (value : Option ValueRef) (children : List (Nat × Hash)) (digit : Nat) (rest : List Nat)
    (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children))
    (hkey : nibbles query.key = digit :: rest)
    (hselected : children.find? (fun pair : Nat × Hash => pair.1 == digit) = none) :
    lookup witness root previous query = .ok {
      reference := none, value := none,
      state := if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query } := by
  have hw := walkObjects_branch_miss witness root bytes value children digit rest
    (queryStart previous query) [] query.accountNodes witness.length hroot rfl hfetch hdecode hselected
  unfold walkObjects queryStart at hw
  simp only [lookup, hkey, hw, bind, Except.bind, pure, Except.pure]
  rfl

/-- A branch without a terminal value returns absence for an empty key,
independently of the query's dereference mode. -/
theorem lookup_branch_empty_none (witness : Witness) (root : Hash) (bytes : Bytes)
    (children : List (Nat × Hash)) (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch none children))
    (hkey : nibbles query.key = []) :
    lookup witness root previous query = .ok {
      reference := none, value := none,
      state := if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query } := by
  have hw := walkObjects_branch_empty witness root bytes none children (queryStart previous query)
    [] query.accountNodes witness.length hroot rfl hfetch hdecode
  unfold walkObjects queryStart at hw
  simp only [lookup, hkey, hw, bind, Except.bind, pure, Except.pure]
  rfl

/-- The branch's own value is separately fetched and length checked. -/
theorem lookup_branch_empty_value (witness : Witness) (root : Hash) (bytes found : Bytes)
    (reference : ValueRef) (children : List (Nat × Hash)) (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch (some reference) children))
    (hkey : nibbles query.key = [])
    (hvalue : fetchObject witness reference.hash = .ok found) (hlength : found.length = reference.length)
    (hmode : query.dereference = true) :
    lookup witness root previous query = .ok {
      reference := some reference, value := some found,
      state := (if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query).touch reference.hash "value" } := by
  let touched := if query.accountNodes then (queryStart previous query).touch root "node"
    else queryStart previous query
  have hw := walkObjects_branch_empty witness root bytes (some reference) children (queryStart previous query)
    [] query.accountNodes witness.length hroot rfl hfetch hdecode
  unfold walkObjects queryStart at hw
  have hd := dereference_binding witness reference found touched hvalue hlength
  simp only [lookup, hkey, hw, bind, Except.bind, hmode, ↓reduceIte]
  change (do let (bytes, state) ← dereference witness reference touched
             pure ({ reference := some reference, value := some bytes, state } : Result)) = _
  rw [hd]
  rfl

/-- A selected child's result is dereferenced only after the complete child
walk, with exact cache/accounting state and the separately bound value. -/
theorem lookup_branch_child_value (witness : Witness) (root child : Hash) (bytes found : Bytes)
    (value : Option ValueRef) (reference : ValueRef) (children : List (Nat × Hash))
    (digit : Nat) (rest : List Nat) (previous after : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.branch value children))
    (hkey : nibbles query.key = digit :: rest)
    (hselected : children.find? (fun pair : Nat × Hash => pair.1 == digit) = some (digit, child))
    (hchild : walkObjects witness query.accountNodes witness.length [root] child rest
      (if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query) = .ok (some reference, after))
    (hvalue : fetchObject witness reference.hash = .ok found) (hlength : found.length = reference.length)
    (hmode : query.dereference = true) :
    lookup witness root previous query = .ok {
      reference := some reference, value := some found, state := after.touch reference.hash "value" } := by
  have hw := walkObjects_branch_child witness root child bytes value (some reference) children digit rest
    (queryStart previous query) after [] query.accountNodes witness.length hroot rfl hfetch hdecode hselected hchild
  unfold walkObjects queryStart at hw
  have hd := dereference_binding witness reference found after hvalue hlength
  simp only [lookup, hkey, hw, bind, Except.bind, hmode, ↓reduceIte]
  change (do let (bytes, state) ← dereference witness reference after
             pure ({ reference := some reference, value := some bytes, state } : Result)) = _
  rw [hd]
  rfl

end Near.TrieBranchLookup
