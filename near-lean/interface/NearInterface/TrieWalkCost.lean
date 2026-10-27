import Lean.Meta.Tactic.Split
import NearInterface.TrieBranchLookup
import NearInterface.TrieExtension

/-!
# Successful trie-walk access bounds

The actual decoder rejects empty extension paths. Branch traversal consumes
one nibble, so every successful walk touches at most one node per query nibble
plus its terminal node. These bounds need no canonical-construction invariant;
malformed or cyclic inputs may fail, but cannot violate a successful bound.
-/
namespace Near.TrieWalkCost
open TrieAccounting TrieLeaf

local macro "unfold_walk" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") "walk"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

local macro "trie_parser" name:ident : term => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  pure (Lean.mkIdent actual)

/-- Local shape obligation for every extension returned by witness lookup. -/
def NonemptyExtensions (witness : Witness) : Prop :=
  ∀ hash bytes path child, fetchObject witness hash = .ok bytes →
    decodeNode bytes = .ok (.extension path child) → path ≠ []

-- Split parser-result matches without unfolding the byte-reading primitives.
-- This is proof search only; every resulting constructor case is kernel checked.
open Lean Meta Elab Tactic in
elab "split_parser_hyp" : tactic => withMainContext do
  for decl in (← getLCtx) do
    if let some goals ← Lean.Meta.splitLocalDecl? (← getMainGoal) decl.fvarId then
      replaceMainGoal goals
      return
  throwError "no parser match remains"

/-- The actual parser rejects empty extension paths, even if arbitrary value
payloads happen to resemble serialized nodes. -/
theorem decodeNode_extension_nonempty (bytes : Bytes) (path : List Nat) (child : Hash)
    (hdecode : decodeNode bytes = .ok (.extension path child)) : path ≠ [] := by
  intro he
  subst path
  simp only [decodeNode, StateT.run, bind, StateT.bind, pure, Except.pure] at hdecode
  cases ht : ((trie_parser readNat) 1) bytes with
  | error error => simp only [ht, Except.bind] at hdecode; cases hdecode
  | ok pair =>
    obtain ⟨tag, rest⟩ := pair
    simp only [ht, Except.bind] at hdecode
    rcases tag with _ | (_ | (_ | (_ | tag)))
    all_goals
      try simp only [StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure] at hdecode
      repeat' first | contradiction | (split_parser_hyp <;> try simp_all [StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure])
      all_goals subst_vars
      all_goals simp_all


/-- Successful decoding enforces the shape condition for all witness objects,
including objects that are also used as arbitrary contract value payloads. -/
theorem nonemptyExtensions (witness : Witness) : NonemptyExtensions witness :=
  fun _ bytes path child _ hdecode => decodeNode_extension_nonempty bytes path child hdecode

/-- Monotonic counters and an upper bound on total accesses and event growth. -/
structure Accesses (before after : Accounting) (bound : Nat) : Prop where
  disk : before.disk ≤ after.disk
  mem : before.mem ≤ after.mem
  total : after.disk + after.mem ≤ before.disk + before.mem + bound
  events : after.events.length ≤ before.events.length + bound

theorem Accesses.refl (state : Accounting) : Accesses state state 0 := by constructor <;> omega

theorem Accesses.mono {before after : Accounting} {small large : Nat}
    (h : Accesses before after small) (hb : small ≤ large) : Accesses before after large := by
  obtain ⟨hd, hm, ht, he⟩ := h
  constructor <;> omega

theorem Accesses.trans {before middle after : Accounting} {first second : Nat}
    (hfirst : Accesses before middle first) (hsecond : Accesses middle after second) :
    Accesses before after (first + second) := by
  obtain ⟨hd1, hm1, ht1, he1⟩ := hfirst
  obtain ⟨hd2, hm2, ht2, he2⟩ := hsecond
  constructor <;> omega

theorem accesses_touch (state : Accounting) (hash : Hash) (kind : String) :
    Accesses state (state.touch hash kind) 1 := by
  unfold Accounting.touch
  cases hc : state.seen.contains hash <;> constructor <;> simp <;> omega

theorem accesses_node (state : Accounting) (root : Hash) (accountNodes : Bool) :
    Accesses state (if accountNodes then state.touch root "node" else state)
      (if accountNodes then 1 else 0) := by
  cases accountNodes
  · exact Accesses.refl state
  · exact accesses_touch state root "node"

private theorem finish_accesses (state : Accounting) (root : Hash) (accountNodes : Bool) (key : List Nat) :
    Accesses state (if accountNodes then state.touch root "node" else state)
      (if accountNodes then key.length + 1 else 0) :=
  (accesses_node state root accountNodes).mono (by cases accountNodes <;> simp)

private theorem child_accesses (state after : Accounting) (root : Hash) (accountNodes : Bool)
    (key tail : List Nat) (hshort : tail.length < key.length)
    (h : Accesses (if accountNodes then state.touch root "node" else state) after
      (if accountNodes then tail.length + 1 else 0)) :
    Accesses state after (if accountNodes then key.length + 1 else 0) := by
  apply ((accesses_node state root accountNodes).trans h).mono
  cases accountNodes <;> simp_all <;> omega

/-- Successful actual traversal: disk/memory counts never decrease and node
access/event growth is bounded by the remaining key length plus one. -/
theorem walk_accesses (witness : Witness) (hnonempty : NonemptyExtensions witness)
    (accountNodes : Bool) (fuel : Nat) (ancestors : List Hash) (root : Hash)
    (key : List Nat) (state after : Accounting) (reference : Option ValueRef)
    (hwalk : walkObjects witness accountNodes fuel ancestors root key state = .ok (reference, after)) :
    Accesses state after (if accountNodes then key.length + 1 else 0) := by
  induction fuel generalizing ancestors root key state after reference with
  | zero =>
    unfold walkObjects at hwalk
    unfold_walk
    cases hwalk
  | succ fuel ih =>
    unfold walkObjects at hwalk
    unfold_walk
    by_cases hz : root == List.replicate 32 0
    · simp only [hz, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hwalk
      obtain ⟨rfl, rfl⟩ := hwalk
      exact (Accesses.refl state).mono (by cases accountNodes <;> simp)
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hwalk
      cases hc : ancestors.contains root with
      | true =>
        simp only [hc, ↓reduceIte] at hwalk
        cases hwalk
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hwalk
        cases hf : fetchObject witness root with
        | error error =>
          unfold fetchObject at hf
          simp [hf, bind, Except.bind] at hwalk
        | ok bytes =>
          have hfetch := hf
          unfold fetchObject at hf
          simp only [hf, bind, Except.bind] at hwalk
          cases hd : decodeNode bytes with
          | error error => simp [hd] at hwalk
          | ok node =>
            simp only [hd] at hwalk
            cases node with
            | leaf path value =>
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hwalk
              obtain ⟨_, rfl⟩ := hwalk
              exact finish_accesses state root accountNodes key
            | extension path child =>
              cases hp : path.isPrefixOf key with
              | false =>
                simp only [hp, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
                  Except.ok.injEq, Prod.mk.injEq] at hwalk
                obtain ⟨_, rfl⟩ := hwalk
                exact finish_accesses state root accountNodes key
              | true =>
                simp only [hp, ↓reduceIte] at hwalk
                have hpath := hnonempty root bytes path child hfetch hd
                have hlen : 0 < path.length := List.length_pos_iff.mpr hpath
                have hpre : path.length ≤ key.length := List.IsPrefix.length_le
                  (List.isPrefixOf_iff_prefix.mp hp)
                apply child_accesses state after root accountNodes key (key.drop path.length)
                  (by simp only [List.length_drop]; omega)
                exact ih (root :: ancestors) child (key.drop path.length) _ after reference hwalk
            | branch value children =>
              cases key with
              | nil =>
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hwalk
                obtain ⟨_, rfl⟩ := hwalk
                exact finish_accesses state root accountNodes []
              | cons digit rest =>
                cases hs : children.find? (·.1 == digit) with
                | none =>
                  simp only [hs, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hwalk
                  obtain ⟨_, rfl⟩ := hwalk
                  exact finish_accesses state root accountNodes (digit :: rest)
                | some pair =>
                  obtain ⟨selected, child⟩ := pair
                  simp only [hs] at hwalk
                  apply child_accesses state after root accountNodes (digit :: rest) rest (by simp)
                  exact ih (root :: ancestors) child rest _ after reference hwalk

/-- A successful value dereference adds exactly one value touch, separately
from whether node accounting was enabled during the preceding walk. -/
theorem dereference_accesses (witness : Witness) (reference : ValueRef)
    (state after : Accounting) (value : Bytes)
    (hread : dereference witness reference state = .ok (value, after)) : Accesses state after 1 := by
  unfold dereference at hread
  cases hf : fetchObject witness reference.hash with
  | error error =>
    unfold fetchObject at hf
    simp [hf, bind, Except.bind] at hread
  | ok bytes =>
    unfold fetchObject at hf
    simp only [hf, bind, Except.bind] at hread
    by_cases hl : bytes.length = reference.length
    · simp only [bne_iff_ne, hl, ne_eq, not_true_eq_false, ↓reduceIte,
        pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hread
      obtain ⟨_, rfl⟩ := hread
      exact accesses_touch state reference.hash "value"
    · simp [hl] at hread

/-- Maximum node accesses for one byte-key query (two nibbles per byte). -/
def nodeBound (query : Query) : Nat := if query.accountNodes then 2 * query.key.length + 1 else 0

/-- Actual successful lookup, including optional value dereference. The
additional value touch is present precisely when returned value bytes exist. -/
theorem lookup_accesses (witness : Witness) (hnonempty : NonemptyExtensions witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) :
    Accesses (queryStart previous query) result.state
      (nodeBound query + if result.value.isSome then 1 else 0) := by
  cases hw : walkObjects witness query.accountNodes (witness.length + 1) [] root
      (nibbles query.key) (queryStart previous query) with
  | error error =>
    unfold walkObjects queryStart at hw
    simp [lookup, hw, bind, Except.bind] at hlookup
  | ok pair =>
    obtain ⟨reference, after⟩ := pair
    have hc := walk_accesses witness hnonempty query.accountNodes (witness.length + 1) [] root
      (nibbles query.key) (queryStart previous query) after reference hw
    have hnodes := TrieConstruction.nibbles_length query.key
    rw [hnodes] at hc
    change Accesses (queryStart previous query) after (nodeBound query) at hc
    unfold walkObjects queryStart at hw
    simp only [lookup, hw, bind, Except.bind] at hlookup
    cases reference with
    | none =>
      cases hlookup
      exact hc
    | some reference =>
      cases hm : query.dereference with
      | false =>
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at hlookup
        cases hlookup
        exact hc
      | true =>
        simp only [hm, ↓reduceIte] at hlookup
        cases hd : dereference witness reference after with
        | error error => simp [hd] at hlookup
        | ok pair =>
          obtain ⟨value, final⟩ := pair
          simp only [hd] at hlookup
          cases hlookup
          exact hc.trans (dereference_accesses witness reference after final value hd)

/-- Query initialization resets counters/events while retaining the chosen
cache. A successful lookup therefore reports at most its own access budget. -/
theorem lookup_total_events (witness : Witness) (hnonempty : NonemptyExtensions witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) :
    result.state.disk + result.state.mem ≤ nodeBound query + (if result.value.isSome then 1 else 0) ∧
    result.state.events.length ≤ nodeBound query + (if result.value.isSome then 1 else 0) := by
  have hc := lookup_accesses witness hnonempty root previous query result hlookup
  constructor
  · simpa only [queryStart, Nat.zero_add] using hc.total
  · simpa only [queryStart, List.length_nil, Nat.zero_add] using hc.events

/-- With node accounting enabled the familiar byte-key bound is `2*n+1`,
plus one only when lookup successfully dereferenced a present value. -/
theorem lookup_total_events_accounted (witness : Witness) (hnonempty : NonemptyExtensions witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) (haccount : query.accountNodes = true) :
    result.state.disk + result.state.mem ≤ 2 * query.key.length + 1 + (if result.value.isSome then 1 else 0) ∧
    result.state.events.length ≤ 2 * query.key.length + 1 + (if result.value.isSome then 1 else 0) := by
  simpa only [nodeBound, haccount, ↓reduceIte] using
    lookup_total_events witness hnonempty root previous query result hlookup

/-- Disabling node accounting leaves both node counters unchanged; no new
node events can appear in a successful walk. Value dereference is separate. -/
theorem walk_unaccounted_counters (witness : Witness) (hnonempty : NonemptyExtensions witness)
    (fuel : Nat) (ancestors : List Hash) (root : Hash) (key : List Nat)
    (state after : Accounting) (reference : Option ValueRef)
    (hwalk : walkObjects witness false fuel ancestors root key state = .ok (reference, after)) :
    after.disk = state.disk ∧ after.mem = state.mem ∧ after.events.length ≤ state.events.length := by
  have hc := walk_accesses witness hnonempty false fuel ancestors root key state after reference hwalk
  obtain ⟨hd, hm, ht, he⟩ := hc
  simp only [Bool.false_eq_true, ↓reduceIte] at ht he
  constructor
  · omega
  constructor
  · omega
  · omega

/-- A lookup with node accounting disabled can still record its separately
requested value dereference; otherwise its per-query access count is zero. -/
theorem lookup_unaccounted (witness : Witness) (hnonempty : NonemptyExtensions witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) (haccount : query.accountNodes = false) :
    result.state.disk + result.state.mem ≤ (if result.value.isSome then 1 else 0) ∧
    result.state.events.length ≤ (if result.value.isSome then 1 else 0) := by
  simpa only [nodeBound, haccount, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using
    lookup_total_events witness hnonempty root previous query result hlookup

/-- The parser's nonempty-extension guard discharges the shape invariant;
this actual successful-walk bound has no witness well-formedness hypothesis. -/
theorem walk_accesses_unconditional (witness : Witness)
    (accountNodes : Bool) (fuel : Nat) (ancestors : List Hash) (root : Hash)
    (key : List Nat) (state after : Accounting) (reference : Option ValueRef)
    (hwalk : walkObjects witness accountNodes fuel ancestors root key state = .ok (reference, after)) :
    Accesses state after (if accountNodes then key.length + 1 else 0) :=
  walk_accesses witness (nonemptyExtensions witness) accountNodes fuel ancestors root key state after reference hwalk

/-- Actual successful lookup bound with the parser shape check discharged. -/
theorem lookup_accesses_unconditional (witness : Witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) :
    Accesses (queryStart previous query) result.state
      (nodeBound query + if result.value.isSome then 1 else 0) :=
  lookup_accesses witness (nonemptyExtensions witness) root previous query result hlookup

theorem lookup_total_events_unconditional (witness : Witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) :
    result.state.disk + result.state.mem ≤ nodeBound query + (if result.value.isSome then 1 else 0) ∧
    result.state.events.length ≤ nodeBound query + (if result.value.isSome then 1 else 0) :=
  lookup_total_events witness (nonemptyExtensions witness) root previous query result hlookup

theorem lookup_total_events_accounted_unconditional (witness : Witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) (haccount : query.accountNodes = true) :
    result.state.disk + result.state.mem ≤ 2 * query.key.length + 1 + (if result.value.isSome then 1 else 0) ∧
    result.state.events.length ≤ 2 * query.key.length + 1 + (if result.value.isSome then 1 else 0) :=
  lookup_total_events_accounted witness (nonemptyExtensions witness) root previous query result hlookup haccount

theorem lookup_unaccounted_unconditional (witness : Witness)
    (root : Hash) (previous : Accounting) (query : Query) (result : Result)
    (hlookup : lookup witness root previous query = .ok result) (haccount : query.accountNodes = false) :
    result.state.disk + result.state.mem ≤ (if result.value.isSome then 1 else 0) ∧
    result.state.events.length ≤ (if result.value.isSome then 1 else 0) :=
  lookup_unaccounted witness (nonemptyExtensions witness) root previous query result hlookup haccount

end Near.TrieWalkCost
