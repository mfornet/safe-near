import NearInterface.TrieLeaf

/-!
# Extension-node decoding and one-step traversal

The actual parser and walker are used throughout. Child traversal remains a
local recursive contract, with fuel and ancestor state explicit. No hash
injectivity or complete host execution is assumed.
-/
namespace Near.TrieExtension
open TrieAccounting TrieConstruction TrieSerialization TrieLeaf

local macro "unfold_trie_reader" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))

/-- Parser composition for the actual extension variant. -/
theorem decodeNode_extension_of_reads (bytes afterTag afterPath afterChild : Bytes)
    (path : List Nat) (child : Hash) (usage : Nat) (hnonempty : path ≠ [])
    (htag : (takeNat 1).run bytes = .ok (3, afterTag))
    (hpath : (takePath false).run afterTag = .ok (path, afterPath))
    (hchild : (takeBytes 32).run afterPath = .ok (child, afterChild))
    (husage : (takeNat 8).run afterChild = .ok (usage, [])) :
    decodeNode bytes = .ok (.extension path child) := by
  simp only [takeNat, takePath, takeBytes, StateT.run] at htag hpath hchild husage
  simp only [decodeNode, StateT.run, bind, StateT.bind]
  rw [htag]
  try simp only [bind, Except.bind, StateT.bind, pure, Except.pure]
  rw [hpath]
  simp only [List.isEmpty_eq_false_iff.mpr hnonempty, Bool.false_eq_true, ↓reduceIte]
  simp only [StateT.bind, StateT.pure]
  rw [hchild]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [husage]
  rfl

/-- Extension encoding round-trips with path, hash, and usage widths explicit. -/
theorem decodeNode_extension (path : List Nat) (child : Hash) (usage : Nat)
    (hpath : ValidPath path) (hnonempty : path ≠ [])
    (hpathRoom : (encodePath false path).length < 2 ^ 32)
    (hhash : child.length = 32) (husageRoom : usage < 2 ^ 64) :
    decodeNode ([3] ++ vectorBytes (encodePath false path) ++ child ++ littleEndian 8 usage) =
      .ok (.extension path child) := by
  apply decodeNode_extension_of_reads _
    (vectorBytes (encodePath false path) ++ (child ++ littleEndian 8 usage))
    (child ++ littleEndian 8 usage) (littleEndian 8 usage) path child usage hnonempty
  · simpa [List.append_assoc] using
      takeNat_append [3] (vectorBytes (encodePath false path) ++ (child ++ littleEndian 8 usage))
  · exact takePath_encoded false path _ hpath hpathRoom
  · have h := takeBytes_append child (littleEndian 8 usage)
    rw [hhash] at h
    exact h
  · simpa using takeNat_little8 usage [] husageRoom

/-- A matching extension consumes its path and one unit of fuel, retains the
ancestor-cycle guard, and passes the touched accounting state to the child. -/
theorem walkObjects_extension (witness : Witness) (root child : Hash) (bytes : Bytes)
    (path key : List Nat) (state : Accounting) (ancestors : List Hash)
    (accountNodes : Bool) (fuel : Nat)
    (hroot : root ≠ List.replicate 32 0) (hcycle : ancestors.contains root = false)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.extension path child)) :
    walkObjects witness accountNodes (fuel + 1) ancestors root key state =
      if path.isPrefixOf key then
        walkObjects witness accountNodes fuel (root :: ancestors) child (key.drop path.length)
          (if accountNodes then state.touch root "node" else state)
      else .ok (none, if accountNodes then state.touch root "node" else state) := by
  generalize hresult : (if path.isPrefixOf key then
    walkObjects witness accountNodes fuel (root :: ancestors) child (key.drop path.length)
      (if accountNodes then state.touch root "node" else state)
    else Except.ok (none, if accountNodes then state.touch root "node" else state)) = result
  unfold walkObjects
  unfold_trie_reader walk
  unfold fetchObject at hfetch
  simp only [beq_eq_false_iff_ne.mpr hroot, Bool.false_eq_true, ↓reduceIte,
    hcycle, bind, Except.bind, hfetch, hdecode, pure, Except.pure]
  unfold walkObjects at hresult
  exact hresult

/-- Successful child traversal is a sufficient local obligation for traversal
through the extension; the child may itself be any trie shape. -/
theorem walkObjects_extension_child (witness : Witness) (root child : Hash) (bytes : Bytes)
    (path key : List Nat) (state after : Accounting) (ancestors : List Hash)
    (accountNodes : Bool) (fuel : Nat) (reference : Option ValueRef)
    (hroot : root ≠ List.replicate 32 0) (hcycle : ancestors.contains root = false)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.extension path child))
    (hprefix : path.isPrefixOf key = true)
    (hchild : walkObjects witness accountNodes fuel (root :: ancestors) child (key.drop path.length)
      (if accountNodes then state.touch root "node" else state) = .ok (reference, after)) :
    walkObjects witness accountNodes (fuel + 1) ancestors root key state = .ok (reference, after) := by
  rw [walkObjects_extension witness root child bytes path key state ancestors accountNodes fuel
    hroot hcycle hfetch hdecode, hprefix]
  exact hchild

/-- A nonmatching extension terminates with absence and just its own touch. -/
theorem walkObjects_extension_miss (witness : Witness) (root child : Hash) (bytes : Bytes)
    (path key : List Nat) (state : Accounting) (ancestors : List Hash)
    (accountNodes : Bool) (fuel : Nat)
    (hroot : root ≠ List.replicate 32 0) (hcycle : ancestors.contains root = false)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.extension path child))
    (hprefix : path.isPrefixOf key = false) :
    walkObjects witness accountNodes (fuel + 1) ancestors root key state =
      .ok (none, if accountNodes then state.touch root "node" else state) := by
  rw [walkObjects_extension witness root child bytes path key state ancestors accountNodes fuel
    hroot hcycle hfetch hdecode, hprefix]
  rfl

/-- Reference-only lookup through an extension uses the actual recursive child
walk and exactly the top-level query cache/reset initialization. -/
theorem lookup_extension_reference (witness : Witness) (root child : Hash) (bytes : Bytes)
    (path : List Nat) (previous after : Accounting) (query : Query) (reference : Option ValueRef)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.extension path child))
    (hprefix : path.isPrefixOf (nibbles query.key) = true)
    (hchild : walkObjects witness query.accountNodes witness.length [root] child
      ((nibbles query.key).drop path.length)
      (if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query) = .ok (reference, after))
    (hmode : query.dereference = false) :
    lookup witness root previous query = .ok { reference, value := none, state := after } := by
  have hw := walkObjects_extension_child witness root child bytes path (nibbles query.key)
    (queryStart previous query) after [] query.accountNodes witness.length reference
    hroot rfl hfetch hdecode hprefix hchild
  unfold walkObjects queryStart at hw
  simp only [lookup, hw, bind, Except.bind]
  cases reference <;> simp [hmode, pure, Except.pure]

/-- A mismatching extension gives absence without a child-trie premise. -/
theorem lookup_extension_miss (witness : Witness) (root child : Hash) (bytes : Bytes)
    (path : List Nat) (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.extension path child))
    (hprefix : path.isPrefixOf (nibbles query.key) = false) :
    lookup witness root previous query = .ok {
      reference := none, value := none,
      state := if query.accountNodes then (queryStart previous query).touch root "node"
        else queryStart previous query } := by
  have hw := walkObjects_extension_miss witness root child bytes path (nibbles query.key)
    (queryStart previous query) [] query.accountNodes witness.length hroot rfl hfetch hdecode hprefix
  unfold walkObjects queryStart at hw
  simp only [lookup, hw, bind, Except.bind, pure, Except.pure]
  rfl

end Near.TrieExtension
