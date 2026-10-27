import NearInterface.TrieOverlay
import Batteries.Tactic.OpenPrivate

/-!
# The storage lookup phase over a canonical trie

The NEAR storage host functions run an external storage phase
(`NearVM.Metered.prepareStorageCallAux`) over a `Near.TrieOverlay.State`:
`getReference` walks the Merkle witness of the base from its root
(`TrieAccounting.lookup`), `dereference` fetches the value object, and the
phase charges the `disk`/`mem` deltas and reports an execution issue if the
lookup errors or disagrees with the host's `storage`. At the boundary the base
is canonical (`Context.WF.trie_canonical : build ctx.trie.entries = .ok
ctx.trie.base`). This file proves that, over such a base, the phase is exact
and cheap.

## Main statements

* `storage_lookup` — for `s` with `build s.entries = .ok s.base`, no witness
  object hashing to the all-zero sentinel (`zeroHash ∉ s.base.witness.map
  Prod.fst`) and a key `k` the overlay does not mention
  (`∀ e ∈ s.prospective, e.1 ≠ k`, same for `committed`):
  - `getReference s k b = .ok (s', ptr)` where `ptr` is
    `((s.entries.find? (·.1 == k)).map (·.2)).map (.trie s.base.root ∘ refOf)`:
    no error, and present iff `k` has a value (its first binding, as the
    host's `storage := find? (·.1 == k)`);
  - `SameData s s'`: entries, base, prospective and committed are unchanged;
    only the accounting (counters, events, hash cache) moves;
  - `disk` and `mem` grow by `d`, `m` with `d + m ≤ 2·|k| + 1` (one access per
    node on the nibble path; zero when nodes are not accounted, `b = false`);
  - for the value `v`, `dereference s' (.trie s.base.root (refOf v)) =
    .ok (s'', v)` with `SameData s' s''` and exactly one more access
    (`dereference_counters`: `d + m = 1`).
* `start_spec` — `start entries` produces such a state (empty overlay,
  canonical base).
* `getReference_prospective` — a prospective overlay hit costs nothing and
  leaves the state unchanged.

The cost bounds hold for any witness, canonical or not: `walk_cost`,
`lookup_cost`, `getReference_cost`, `dereference_cost'`. They rest on the
decoder rejecting empty extensions (`decodeNode_extension`), so every node
visit consumes at least one nibble of the `2·|k|`-nibble key or ends the walk.

## Why correctness holds

* `Rep W A h f` says the witness `W`, walked from `h` with ancestors `A`,
  represents the map `f` from nibble paths to values; `walk_rep` /
  `getReference_rep` show the walk computes `f` exactly (fuel
  `|W| + 1` suffices since ancestors are distinct witness keys).
* `construct_rep` is the lookup-after-build lemma, by induction on the
  construction fuel, for the three node shapes (leaf, extension, branch):
  - the encodings decode back (`decodeNode_leaf`,
    `decodeNode_extension_run`, `decodeNode_branch_none/some`, through
    `readNat_run`, `decodePath_encodePath`, `readChildren_run`; the child
    mask is tracked by `Bits` through both 16-nibble loops, `build_loop` and
    `children_loop`);
  - `build`'s dedup loop leaves one binding per hash containing every object
    (`build_spec`, `dedup_inv`), so `fetch` returns each object's bytes; no
    collision resistance is assumed, since `build` itself rejects collisions;
  - the cycle check never fires: every node object ends with its subtree
    usage, strictly larger than its children's (`Big`, `not_anc`);
  - the denoted map is the entries' first-binding map (`sem`, `sem_leaf`,
    `sem_ext`, `sem_branch_nil/cons`; `sem_nibbles` by injectivity of
    `nibbles`).

## The one assumption

`walk` treats the hash `List.replicate 32 0` as the empty trie. If some
object's SHA-256 were all zeros the walk would stop early, so the theorems
assume `zeroHash ∉ s.base.witness.map Prod.fst`. This is a statement about
SHA-256 preimages, not provable here, but decidable for any concrete state.

Not covered: relating `s.entries.find? (·.1 == contractKey account key)` to
the VM host's `storage key` (that is `Context.WF.trie_storage` plus
`toNearState`), and states whose base came from a `checkpoint` (covered too
whenever `build entries = .ok base` holds, which `checkpoint` establishes).
-/

namespace NearLogic
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open private walk fetch readPath readBytes readNat readRef readChildren from NearInterface.TrieAccounting
open private overlay from NearInterface.TrieOverlay
open private little vector pack finish construct common refBytes from NearInterface.TrieConstruction

/-! ## Cost: any witness -/

/-- Every successful run of the parser returns a value satisfying `Q`. -/
def Sat {α} (p : Parser α) (Q : α → Prop) : Prop :=
  ∀ s a s', p s = .ok (a, s') → Q a

theorem Sat.bind {α β} {p : Parser α} {f : α → Parser β} {Q : β → Prop}
    (h : ∀ a, Sat (f a) Q) : Sat (p >>= f) Q := by
  intro s b s' hb
  have e : (p >>= f) s = (match p s with | .error e => .error e | .ok (a, s) => f a s) := by
    show StateT.bind p f s = _
    simp only [StateT.bind, Bind.bind, Except.bind]
    generalize p s = r
    rcases r with _ | ⟨a, s⟩ <;> rfl
  rw [e] at hb
  split at hb
  · cases hb
  · exact h _ _ _ _ hb

theorem Sat.pure {α} {a : α} {Q : α → Prop} (h : Q a) : Sat (pure a) Q := by
  intro s b s' hb
  have e : (Pure.pure a : Parser α) s = .ok (a, s) := rfl
  rw [e] at hb
  cases hb; exact h

theorem Sat.err {α} {p : Parser α} {Q : α → Prop} (h : ∀ s, ∃ e, p s = .error e) : Sat p Q := by
  intro s b s' hb
  obtain ⟨e, he⟩ := h s
  rw [he] at hb
  cases hb

theorem Sat.ite {α} {c : Prop} [Decidable c] {p q : Parser α} {Q : α → Prop}
    (hp : c → Sat p Q) (hq : ¬ c → Sat q Q) : Sat (if c then p else q) Q := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

theorem Sat.mono {α} {p : Parser α} {Q : α → Prop} (h : ∀ a, Q a) : Sat p Q :=
  fun _ a _ _ => h a

theorem decode_outer {P : Parser Node} {bytes : Bytes} {n : Node}
    (h : (do
      let (node, remaining) ← P.run bytes
      unless remaining.isEmpty do throw "trailing trie node bytes"
      return node : Except String Node) = .ok n) : ∃ s, P bytes = .ok (n, s) := by
  simp only [StateT.run, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h; exact ⟨_, hv⟩
    · cases h

/-- The parsed node of `decodeNode`, as a `Sat` property of its parser. -/
theorem decodeNode_sat {bytes : Bytes} {n : Node} (Q : Node → Prop)
    (hQ : Sat (do
      let tag ← readNat 1
      let node : Node ← match tag with
        | 0 => do
          let path ← readPath true
          let value ← readRef
          pure (.leaf path value)
        | 1 => do pure (.branch none (← readChildren))
        | 2 => do
          let value ← readRef
          pure (.branch (some value) (← readChildren))
        | 3 => do
          let path ← readPath false
          if path.isEmpty then throw "empty trie extension"
          pure (.extension path (← readBytes 32))
        | _ => throw "unknown trie node variant"
      let _ ← readNat 8
      return node : Parser Node) Q)
    (h : decodeNode bytes = .ok n) : Q n := by
  unfold decodeNode at h
  obtain ⟨s, hs⟩ := decode_outer h
  exact hQ _ _ _ hs

theorem decodeNode_extension {bytes : Bytes} {path : List Nat} {child : Hash}
    (h : decodeNode bytes = .ok (.extension path child)) : path ≠ [] := by
  refine decodeNode_sat (fun n => ∀ p c, n = .extension p c → p ≠ []) ?_ h _ _ rfl
  refine Sat.bind fun tag => ?_
  dsimp only
  split
  all_goals repeat (first
    | exact Sat.err fun _ => ⟨_, rfl⟩
    | exact Sat.pure (by simp_all)
    | (apply Sat.ite <;> intro hc)
    | (rw [pure_bind])
    | (apply Sat.bind; intro))

/-- The number of accounted trie accesses so far (fresh plus cached). -/
def cost (st : Accounting) : Nat := st.disk + st.mem

theorem cost_touch (st : Accounting) (h : Hash) (k : String) :
    cost (st.touch h k) = cost st + 1 := Accounting.touch_total st h k

theorem walk_cost (W : Witness) (a : Bool) :
    ∀ (fuel : Nat) (anc : List Hash) (h : Hash) (key : List Nat) (st st' : Accounting)
      (r : Option ValueRef), walk W a fuel anc h key st = .ok (r, st') →
      cost st' ≤ cost st + (key.length + 1) ∧ (a = false → st' = st) := by
  intro fuel
  induction fuel with
  | zero => intro anc h key st st' r hw; rw [walk] at hw; cases hw
  | succ fuel ih =>
    intro anc h key st st' r hw
    rw [walk] at hw
    simp only [bind, Except.bind, pure, Except.pure] at hw
    have h1 : cost (if a = true then st.touch h "node" else st) ≤ cost st + 1 ∧
        (a = false → (if a = true then st.touch h "node" else st) = st) := by
      cases a <;> simp [cost_touch]
    generalize (if a = true then st.touch h "node" else st) = st₁ at hw h1
    split at hw
    · cases hw; simp
    split at hw
    · cases hw
    split at hw
    · cases hw
    split at hw
    · cases hw
    split at hw
    · cases hw; exact ⟨by omega, h1.2⟩
    · rename_i bytes _ path child hdec
      have hne := decodeNode_extension hdec
      split at hw
      · rename_i hp
        have hpl : path.length ≤ key.length := (List.isPrefixOf_iff_prefix.mp hp).length_le
        have hr := ih _ _ _ _ _ _ hw
        have : path.length ≠ 0 := by simpa using hne
        simp only [List.length_drop] at hr
        exact ⟨by omega, fun ha => (hr.2 ha).trans (h1.2 ha)⟩
      · cases hw; exact ⟨by omega, h1.2⟩
    · split at hw
      · cases hw; exact ⟨by omega, h1.2⟩
      · split at hw
        · cases hw; simp only [List.length_cons]; exact ⟨by omega, h1.2⟩
        · have := ih _ _ _ _ _ _ hw
          simp only [List.length_cons]
          exact ⟨by omega, fun ha => (this.2 ha).trans (h1.2 ha)⟩

theorem nibbles_length (k : Bytes) : (nibbles k).length = 2 * k.length := by
  induction k with
  | nil => rfl
  | cons b k ih =>
    simp only [nibbles, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

theorem dereference_cost {W : Witness} {r : ValueRef} {st st' : Accounting} {v : Bytes}
    (h : Near.TrieAccounting.dereference W r st = .ok (v, st')) : cost st' = cost st + 1 :=
  dereference_success_total W r st st' v h

/-- Lookup's per-query counters: at most one access per key nibble plus one,
and one more when the value is dereferenced. -/
theorem lookup_cost {W : Witness} {root : Hash} {prev : Accounting} {q : Query} {res : Result}
    (h : lookup W root prev q = .ok res) :
    cost res.state ≤ 2 * q.key.length + 1 + (if q.dereference then 1 else 0) ∧
      (q.accountNodes = false → q.dereference = false → cost res.state = 0) := by
  unfold lookup at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i v hv
  obtain ⟨hc, hz⟩ := walk_cost W _ _ _ _ _ _ _ _ hv
  rw [nibbles_length] at hc
  have h0 : cost ({ seen := if q.resetCache = true then [] else prev.seen } : Accounting) = 0 := rfl
  split at h
  · split at h
    · split at h
      · cases h
      · cases h
        rename_i hd _ _ hdr
        have := dereference_cost hdr
        simp only [hd, ↓reduceIte]
        refine ⟨by omega, fun _ hf => by simp at hf⟩
    · cases h
      rename_i hd
      simp only [hd]
      refine ⟨by omega, fun ha _ => ?_⟩
      rw [hz ha]; rfl
  · cases h
    refine ⟨by dsimp only; split <;> omega, fun ha _ => ?_⟩
    simp only
    rw [hz ha]; rfl

/-- Two overlay states agree on everything but the accounting (counters,
events and the hash cache). -/
def SameData (s s' : State) : Prop :=
  s'.entries = s.entries ∧ s'.base = s.base ∧ s'.prospective = s.prospective ∧
    s'.committed = s.committed

/-- `getReference` only touches the accounting, adding at most `2·|k| + 1`
accesses (one per node on the nibble path), and none when nodes are not
accounted. -/
theorem getReference_cost {s s' : State} {k : Bytes} {b : Bool} {p : Option ValuePointer}
    (h : getReference s k b = .ok (s', p)) :
    SameData s s' ∧ cost s'.accounting ≤ cost s.accounting + (2 * k.length + 1) ∧
      (b = false → cost s'.accounting = cost s.accounting) := by
  unfold getReference at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, by omega, fun _ => rfl⟩
  · cases h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, by omega, fun _ => rfl⟩
  · split at h
    · cases h
    · cases h
      rename_i res hres
      obtain ⟨hc, hz⟩ := lookup_cost hres
      dsimp only at hc hz
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc
      refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, fun hb => ?_⟩
      · simp only [cost] at hc ⊢; omega
      · have := hz hb rfl
        simp only [cost] at this ⊢; omega

/-- `dereference` only touches the accounting: one access for an on-disk
pointer, none for an overlay value. -/
theorem dereference_cost' {s s' : State} {p : ValuePointer} {v : Bytes}
    (h : Near.TrieOverlay.dereference s p = .ok (s', v)) :
    SameData s s' ∧ cost s'.accounting =
      cost s.accounting + (match p with | .memory _ => 0 | .trie _ _ => 1) := by
  cases p with
  | memory bytes => cases h; exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  | trie root r =>
    unfold Near.TrieOverlay.dereference at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · split at h
      · cases h
      · rename_i hd
        cases h
        exact ⟨⟨rfl, rfl, rfl, rfl⟩, dereference_cost hd⟩
    · split at h
      · cases h
      · rename_i hh; cases hh

/-! ## Lookup correctness over a witness that represents a map -/

def zeroHash : Hash := List.replicate 32 0

/-- The reference a canonical trie stores for a value. -/
def refOf (v : Bytes) : ValueRef := { hash := Near.Sha256.hash v, length := v.length }

/-- The witness serves the value under its hash. -/
def Serves (W : Witness) (v : Bytes) : Prop := fetch W (Near.Sha256.hash v) = .ok v

/-- `Rep W A h f`: walking the witness `W` from the node hash `h`, with
ancestor list `A`, represents the partial map `f` from nibble paths to values.
Node hashes are nonzero, never repeat an ancestor, and decode to nodes whose
children represent the corresponding restrictions of `f`. -/
inductive Rep (W : Witness) : List Hash → Hash → (List Nat → Option Bytes) → Prop
  | empty (A : List Hash) : Rep W A zeroHash fun _ => none
  | leaf (A : List Hash) (h : Hash) (bytes : Bytes) (path : List Nat) (v : Bytes) :
      h ≠ zeroHash → h ∉ A → fetch W h = .ok bytes →
      decodeNode bytes = .ok (.leaf path (refOf v)) → Serves W v →
      Rep W A h fun k => if path = k then some v else none
  | extension (A : List Hash) (h : Hash) (bytes : Bytes) (path : List Nat) (child : Hash)
      (g : List Nat → Option Bytes) :
      h ≠ zeroHash → h ∉ A → fetch W h = .ok bytes →
      decodeNode bytes = .ok (.extension path child) → Rep W (h :: A) child g →
      Rep W A h fun k => if path.isPrefixOf k then g (k.drop path.length) else none
  | branch (A : List Hash) (h : Hash) (bytes : Bytes) (value : Option Bytes)
      (children : List (Nat × Hash)) (g : Nat → List Nat → Option Bytes) :
      h ≠ zeroHash → h ∉ A → fetch W h = .ok bytes →
      decodeNode bytes = .ok (.branch (value.map refOf) children) →
      (∀ v, value = some v → Serves W v) →
      (∀ n p, children.find? (·.1 == n) = some p → Rep W (h :: A) p.2 (g n)) →
      Rep W A h fun k => match k with
        | [] => value
        | n :: rest => if (children.find? (·.1 == n)).isSome then g n rest else none

theorem fetch_mem {W : Witness} {h : Hash} {b : Bytes} (hf : fetch W h = .ok b) :
    h ∈ W.map Prod.fst := by
  unfold fetch at hf
  split at hf
  · rename_i e he
    have hm := List.mem_of_find?_eq_some he
    have hq := List.find?_some he
    simp only [beq_iff_eq] at hq
    exact List.mem_map.mpr ⟨_, hm, hq⟩
  · cases hf

theorem anc_length {W : Witness} {A : List Hash} (hn : A.Nodup) (hs : ∀ x ∈ A, x ∈ W.map Prod.fst) :
    A.length ≤ W.length := by
  have := List.Nodup.length_le_of_subset hn (fun x hx => hs x hx)
  simpa using this

/-- One node visit: the walk's prelude, for a nonzero, non-ancestor hash. -/
theorem walk_node {W : Witness} {a : Bool} {m : Nat} {A : List Hash} {h : Hash} {key : List Nat}
    {st : Accounting} {bytes : Bytes} {node : Node}
    (hz : h ≠ zeroHash) (hA : h ∉ A) (hf : fetch W h = .ok bytes) (hd : decodeNode bytes = .ok node) :
    walk W a (m + 1) A h key st =
      (let st := if a then st.touch h "node" else st
       match node with
       | .leaf path value => .ok (if path == key then some value else none, st)
       | .extension path child =>
         if path.isPrefixOf key then walk W a m (h :: A) child (key.drop path.length) st
         else .ok (none, st)
       | .branch value children =>
         match key with
         | [] => .ok (value, st)
         | nibble :: rest =>
           match children.find? (·.1 == nibble) with
           | none => .ok (none, st)
           | some (_, child) => walk W a m (h :: A) child rest st) := by
  rw [walk]
  have h1 : (h == List.replicate 32 0) = false := by simpa [zeroHash] using hz
  have h2 : A.contains h = false := by simpa using hA
  simp only [h1, h2, hf, hd, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  cases node <;> rfl

/-- Walk correctness: a represented map is looked up exactly, with enough fuel. -/
theorem walk_rep {W : Witness} (a : Bool) {A : List Hash} {h : Hash}
    {f : List Nat → Option Bytes} (hr : Rep W A h f) :
    ∀ (fuel : Nat), A.Nodup → (∀ x ∈ A, x ∈ W.map Prod.fst) → W.length + 1 ≤ fuel + A.length →
      ∀ key st, ∃ st', walk W a fuel A h key st = .ok ((f key).map refOf, st') := by
  induction hr with
  | empty A =>
    intro fuel hn hs hf key st
    have := anc_length hn hs
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    exact ⟨st, by rw [walk]; simp [zeroHash, pure, Except.pure]⟩
  | leaf A h bytes path v hz hA hf hd hs =>
    intro fuel hn hs hfu key st
    have := anc_length hn hs
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    refine ⟨if a then st.touch h "node" else st, ?_⟩
    rw [walk_node hz hA hf hd]
    simp only [beq_iff_eq]
    split <;> simp_all
  | extension A h bytes path child g hz hA hf hd _ ih =>
    intro fuel hn hs hfu key st
    have := anc_length hn hs
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    have hn' : (h :: A).Nodup := List.nodup_cons.mpr ⟨hA, hn⟩
    have hs' : ∀ x ∈ h :: A, x ∈ W.map Prod.fst := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact fetch_mem hf
      · exact hs x hx
    rw [walk_node hz hA hf hd]
    dsimp only
    split
    · exact ih m hn' hs' (by simp; omega) _ _
    · exact ⟨_, rfl⟩
  | branch A h bytes value children g hz hA hf hd _ _ ih =>
    intro fuel hn hs hfu key st
    have := anc_length hn hs
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    have hn' : (h :: A).Nodup := List.nodup_cons.mpr ⟨hA, hn⟩
    have hs' : ∀ x ∈ h :: A, x ∈ W.map Prod.fst := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact fetch_mem hf
      · exact hs x hx
    rw [walk_node hz hA hf hd]
    dsimp only
    cases key with
    | nil => exact ⟨_, rfl⟩
    | cons n rest =>
      dsimp only
      split
      · rename_i hfind
        simp only [hfind, Option.isSome_none]
        exact ⟨_, rfl⟩
      · rename_i c hfind
        simp only [hfind, Option.isSome_some, ↓reduceIte]
        exact ih n _ hfind m hn' hs' (by simp; omega) _ _

theorem Rep.serves {W : Witness} {A : List Hash} {h : Hash} {f : List Nat → Option Bytes}
    (hr : Rep W A h f) : ∀ k v, f k = some v → Serves W v := by
  induction hr with
  | empty => intro k v hk; cases hk
  | leaf A h bytes path v' _ _ _ _ hs =>
    intro k v hk
    dsimp only at hk
    split at hk
    · cases hk; exact hs
    · cases hk
  | extension A h bytes path child g _ _ _ _ _ ih =>
    intro k v hk
    dsimp only at hk
    split at hk
    · exact ih _ _ hk
    · cases hk
  | branch A h bytes value children g _ _ _ _ hv _ ih =>
    intro k v hk
    cases k with
    | nil => exact hv v hk
    | cons n rest =>
      dsimp only at hk
      split at hk
      · rename_i hsome
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
        exact ih n p hp _ _ hk
      · cases hk

theorem serves_dereference {W : Witness} {v : Bytes} (hs : Serves W v) (st : Accounting) :
    Near.TrieAccounting.dereference W (refOf v) st = .ok (v, st.touch (Near.Sha256.hash v) "value") := by
  unfold Near.TrieAccounting.dereference
  simp only [refOf] at *
  unfold Serves at hs
  simp [hs, bind, Except.bind, pure, Except.pure]

theorem overlay_none {s : State} {k : Bytes}
    (hp : ∀ e ∈ s.prospective, e.1 ≠ k) (hc : ∀ e ∈ s.committed, e.1 ≠ k) :
    overlay s k = none := by
  unfold overlay
  have h1 : s.prospective.find? (·.1 == k) = none :=
    List.find?_eq_none.mpr fun e he => by simpa using hp e he
  have h2 : s.committed.find? (·.1 == k) = none :=
    List.find?_eq_none.mpr fun e he => by simpa using hc e he
  simp [h1, h2]

/-- Correctness of the storage lookup phase over a represented base, for a
key the overlay does not mention: no error, the pointer is the on-disk
reference of `f (nibbles k)`, and dereferencing it returns that value. -/
theorem getReference_rep {s : State} {k : Bytes} (b : Bool) {f : List Nat → Option Bytes}
    (hr : Rep s.base.witness [] s.base.root f)
    (hp : ∀ e ∈ s.prospective, e.1 ≠ k) (hc : ∀ e ∈ s.committed, e.1 ≠ k) :
    ∃ s', getReference s k b =
        .ok (s', (f (nibbles k)).map fun v => .trie s.base.root (refOf v)) ∧
      SameData s s' ∧
      ∀ v, f (nibbles k) = some v →
        ∃ s'', Near.TrieOverlay.dereference s' (.trie s.base.root (refOf v)) = .ok (s'', v) ∧
          SameData s' s'' ∧ cost s''.accounting = cost s'.accounting + 1 := by
  have hl : ∃ res, lookup s.base.witness s.base.root s.accounting
      { key := k, accountNodes := b, dereference := false, resetCache := false } = .ok res ∧
      res.reference = (f (nibbles k)).map refOf := by
    unfold lookup
    obtain ⟨st', hw⟩ := walk_rep b hr (s.base.witness.length + 1) List.nodup_nil (by simp) (by simp)
      (nibbles k) { seen := s.accounting.seen }
    simp only [Bool.false_eq_true, ↓reduceIte, hw, bind, Except.bind, pure, Except.pure]
    split <;> rename_i heq <;> exact ⟨_, rfl, heq.symm⟩
  obtain ⟨res, hres, href⟩ := hl
  unfold getReference
  rw [overlay_none hp hc]
  simp only [hres, href, bind, Except.bind, pure, Except.pure, Option.map_map]
  refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl⟩, fun v _ => ?_⟩
  have hs := hr.serves _ _ ‹_›
  refine ⟨?w, ?h1, ?h2⟩
  case h1 =>
    unfold Near.TrieOverlay.dereference
    simp only [serves_dereference hs, bind, Except.bind, pure, Except.pure, BEq.rfl]
    rfl
  case h2 => exact ⟨⟨rfl, rfl, rfl, rfl⟩, cost_touch _ _ _⟩

/-! ## Construction: the deduplicated witness -/

/-- The dedup loop's step, abstractly: append a fresh hash, or keep an
equal binding. -/
def DedupStep (F : Hash × Bytes → Witness → Except String (ForInStep Witness)) : Prop :=
  ∀ x acc r, F x acc = .ok r → ∃ acc', r = .yield acc' ∧
    ((acc.find? (·.1 == x.1) = none ∧ acc' = acc ++ [x]) ∨ (x ∈ acc ∧ acc' = acc))

theorem dedup_inv {F} (hF : DedupStep F) :
    ∀ (l acc U : Witness), forIn l acc F = .ok U → (acc.map Prod.fst).Nodup →
      (U.map Prod.fst).Nodup ∧ (∀ y ∈ acc, y ∈ U) ∧ ∀ x ∈ l, x ∈ U := by
  intro l
  induction l with
  | nil => intro acc U h hn; cases h; exact ⟨hn, fun _ h => h, by simp⟩
  | cons x l ih =>
    intro acc U h hn
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i r hr
    obtain ⟨acc', rfl, hc⟩ := hF _ _ _ hr
    simp only at h
    rcases hc with ⟨hnone, rfl⟩ | ⟨hmem, rfl⟩
    · have hn' : ((acc ++ [x]).map Prod.fst).Nodup := by
        rw [List.map_append, List.nodup_append]
        refine ⟨hn, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        intro hab; subst hab
        obtain ⟨y, hy, hya⟩ := List.mem_map.mp ha
        have := List.find?_eq_none.mp hnone y hy
        simp [hya] at this
      obtain ⟨h1, h2, h3⟩ := ih _ _ h hn'
      refine ⟨h1, fun y hy => h2 y (by simp [hy]), ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h2 z (by simp)
      · exact h3 z hz
    · obtain ⟨h1, h2, h3⟩ := ih _ _ h hn
      refine ⟨h1, h2, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h2 z hmem
      · exact h3 z hz

theorem fetch_of_mem {U : Witness} (hn : (U.map Prod.fst).Nodup) {x : Hash × Bytes} (hx : x ∈ U) :
    fetch U x.1 = .ok x.2 := by
  induction U with
  | nil => cases hx
  | cons y U ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    unfold fetch at ih ⊢
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : y.1 ≠ x.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hx)
      have hb : (y.1 == x.1) = false := by simpa using hne
      simp only [List.find?_cons, hb]
      exact ih hn.2 hx

/-- What `build` establishes: bounded entries, a successful construction,
and a deduplicated witness containing every constructed object. -/
theorem build_spec {e : List (Bytes × Bytes)} {B : Built} (h : build e = .ok B) :
    (∀ x ∈ e, x.1.length < 2 ^ 32 ∧ x.2.length < 2 ^ 32) ∧
    ∃ fuel C, construct fuel (e.map fun x => (nibbles x.1, x.2)) = .ok C ∧
      B.root = C.root ∧ B.memoryUsage = C.memoryUsage ∧
      (B.witness.map Prod.fst).Nodup ∧ ∀ x ∈ C.witness, x ∈ B.witness := by
  unfold build at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · rename_i hh; cases hh
  split at h
  · split at h
    · cases h
    · rename_i hh; cases hh
  rename_i hany
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [Bool.not_eq_true, List.any_eq_false, Bool.or_eq_true, decide_eq_true_eq,
      not_or, Nat.not_le] at hany
    exact hany x hx
  split at h
  · cases h
  rename_i C hC
  split at h
  · cases h
  rename_i U hU
  cases h
  have hD := dedup_inv (l := C.witness) (acc := []) (U := U) ?hD hU (by simp)
  · exact ⟨_, C, hC, rfl, rfl, hD.1, hD.2.2⟩
  intro x acc r hr
  dsimp only at hr
  split at hr
  · rename_i hn
    cases hr
    exact ⟨_, rfl, Or.inl ⟨hn, rfl⟩⟩
  · rename_i fst prev hf
    split at hr
    · split at hr
      · cases hr
      · rename_i hh; cases hh
    · rename_i hne
      cases hr
      refine ⟨_, rfl, Or.inr ⟨?_, rfl⟩⟩
      have hm := List.mem_of_find?_eq_some hf
      have hq := List.find?_some hf
      simp only [beq_iff_eq] at hq
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
      have : x = (fst, prev) := by
        obtain ⟨a, b⟩ := x
        simp_all
      rw [this]; exact hm

/-! ## Construction: decoding the encodings -/

theorem readBytes_run {xs rest : Bytes} {n : Nat} (hn : xs.length = n) :
    readBytes n (xs ++ rest) = .ok (xs, rest) := by
  subst hn
  unfold readBytes
  simp [get, getThe, MonadStateOf.get, StateT.get, set, bind, StateT.bind, pure,
    Except.bind, Except.pure, MonadStateOf.set]
  split
  · omega
  · rfl

theorem little_succ (n v : Nat) : little (n + 1) v = UInt8.ofNat (v % 256) :: little n (v / 256) := by
  unfold little
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    have : v / 2 ^ (8 * (i + 1)) = v / 256 / 2 ^ (8 * i) := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    simp only [Function.comp, this]

theorem little_length (n v : Nat) : (little n v).length = n := by
  unfold little; simp

theorem little_fold (n : Nat) : ∀ v, v < 2 ^ (8 * n) →
    (little n v).foldr (fun byte rest => byte.toNat + 256 * rest) 0 = v := by
  induction n with
  | zero =>
    intro v hv
    obtain rfl : v = 0 := by rw [Nat.mul_zero, Nat.pow_zero] at hv; omega
    rfl
  | succ n ih =>
    intro v hv
    rw [little_succ, List.foldr_cons, ih (v / 256)]
    · rw [UInt8.toNat_ofNat']
      omega
    · rw [Nat.mul_succ, Nat.pow_add] at hv
      exact Nat.div_lt_of_lt_mul (by omega)

theorem readNat_run {n v : Nat} {rest : Bytes} (hv : v < 2 ^ (8 * n)) :
    readNat n (little n v ++ rest) = .ok (v, rest) := by
  unfold readNat
  simp only [bind, StateT.bind, readBytes_run (little_length n v), Except.bind, pure, StateT.pure,
    Except.pure, little_fold n v hv]

theorem nibbles_cons (x : UInt8) (xs : Bytes) :
    nibbles (x :: xs) = x.toNat / 16 :: x.toNat % 16 :: nibbles xs := by
  simp [nibbles]

theorem nibbles_pack : (p : List Nat) → p.length % 2 = 0 → (∀ x ∈ p, x < 16) → nibbles (pack p) = p
  | [], _, _ => rfl
  | [_], h, _ => by simp at h
  | a :: b :: rest, h, hb => by
    have ha : a < 16 := hb a (by simp)
    have hb' : b < 16 := hb b (by simp)
    rw [pack, nibbles_cons, nibbles_pack rest (by simp at h; omega)
      (fun x hx => hb x (by simp [hx]))]
    rw [UInt8.toNat_ofNat']
    congr 2 <;> omega

theorem decodePath_encodePath (leaf : Bool) (p : List Nat) (hp : ∀ x ∈ p, x < 16) :
    decodePath leaf (encodePath leaf p) = .ok p := by
  by_cases hpar : p.length % 2 = 0
  · have hE : encodePath leaf p = UInt8.ofNat (if leaf then 32 else 0) :: pack p := by
      simp [encodePath, hpar]
    rw [hE]
    unfold decodePath
    cases leaf <;> simp [nibbles_pack p hpar hp, pure, Except.pure]
  · obtain ⟨a, t, rfl⟩ : ∃ a t, p = a :: t := by
      cases p with
      | nil => simp at hpar
      | cons a t => exact ⟨a, t, rfl⟩
    have ha : a < 16 := hp a (by simp)
    have ht : t.length % 2 = 0 := by simp at hpar; omega
    have hpt := nibbles_pack t ht (fun x hx => hp x (by simp [hx]))
    have hE : encodePath leaf (a :: t) = UInt8.ofNat ((if leaf then 32 else 0) + 16 + a) :: pack t := by
      simp only [encodePath, beq_iff_eq, hpar, ↓reduceIte, List.tail_cons]
      rfl
    rw [hE]
    unfold decodePath
    have h1 : (16 + a) % 256 / 16 = 1 := by omega
    have h2 : (32 + 16 + a) % 256 / 16 = 3 := by omega
    have h3 : a % 16 = a := by omega
    cases leaf
    · simp [UInt8.toNat_ofNat', hpt, h1, h3, pure, Except.pure]
    · simp [UInt8.toNat_ofNat', hpt, h2, pure, Except.pure]
      omega

theorem run_bind {α β} {p : Parser α} {f : α → Parser β} {s s1 : Bytes} {a : α}
    (h : p s = .ok (a, s1)) : (p >>= f) s = f a s1 := by
  show StateT.bind p f s = _
  simp only [StateT.bind, h]
  rfl

theorem run_pure {α} (a : α) (s : Bytes) : (pure a : Parser α) s = .ok (a, s) := rfl

theorem readPath_run {leaf : Bool} {p : List Nat} {rest : Bytes} (hp : ∀ x ∈ p, x < 16)
    (hl : (encodePath leaf p).length < 2 ^ 32) :
    readPath leaf (vector (encodePath leaf p) ++ rest) = .ok (p, rest) := by
  unfold readPath vector
  rw [List.append_assoc, run_bind (readNat_run hl), run_bind (readBytes_run rfl)]
  simp only [decodePath_encodePath leaf p hp]
  rfl

theorem readRef_run {v rest : Bytes} (hv : v.length < 2 ^ 32) :
    readRef (refBytes v ++ rest) = .ok (refOf v, rest) := by
  unfold readRef refBytes
  rw [List.append_assoc, run_bind (readNat_run hv), run_bind (readBytes_run (Near.Sha256.hash_length v))]
  rfl

theorem decode_of_run {P : Parser Node} {bytes : Bytes} {n : Node} (h : P bytes = .ok (n, [])) :
    (do
      let (node, remaining) ← P.run bytes
      unless remaining.isEmpty do throw "trailing trie node bytes"
      return node : Except String Node) = .ok n := by
  simp only [StateT.run, h]
  rfl

theorem decodeNode_leaf {p : List Nat} {v : Bytes} {u : Nat} (hp : ∀ x ∈ p, x < 16)
    (hl : (encodePath true p).length < 2 ^ 32) (hv : v.length < 2 ^ 32) (hu : u < 2 ^ 64) :
    decodeNode ([0] ++ vector (encodePath true p) ++ refBytes v ++ little 8 u) =
      .ok (.leaf p (refOf v)) := by
  unfold decodeNode
  refine decode_of_run ?_
  have e : [0] ++ vector (encodePath true p) ++ refBytes v ++ little 8 u =
      little 1 0 ++ (vector (encodePath true p) ++ (refBytes v ++ (little 8 u ++ []))) := by
    simp only [List.append_assoc, List.append_nil]; rfl
  rw [e, run_bind (readNat_run (by decide))]
  show (do
    let path ← readPath true
    let value ← readRef
    let node ← pure (Node.leaf path value)
    let _ ← readNat 8
    pure node : Parser Node) _ = _
  rw [run_bind (readPath_run hp hl), run_bind (readRef_run hv), pure_bind,
    run_bind (readNat_run hu)]
  rfl

/-! ## Construction: branch nodes and the child loops -/

theorem decodeNode_extension_run {p : List Nat} {r : Bytes} {u : Nat} (hp : ∀ x ∈ p, x < 16)
    (hne : p ≠ []) (hl : (encodePath false p).length < 2 ^ 32) (hr : r.length = 32) (hu : u < 2 ^ 64) :
    decodeNode ([3] ++ vector (encodePath false p) ++ r ++ little 8 u) =
      .ok (.extension p r) := by
  unfold decodeNode
  refine decode_of_run ?_
  have e : [3] ++ vector (encodePath false p) ++ r ++ little 8 u =
      little 1 3 ++ (vector (encodePath false p) ++ (r ++ (little 8 u ++ []))) := by
    simp only [List.append_assoc, List.append_nil]; rfl
  rw [e, run_bind (readNat_run (by decide))]
  show (do
    let path ← readPath false
    if path.isEmpty then throw "empty trie extension"
    let node ← pure (Node.extension path (← readBytes 32))
    let _ ← readNat 8
    pure node : Parser Node) _ = _
  rw [run_bind (readPath_run hp hl)]
  have : p.isEmpty = false := by cases p <;> simp_all
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  rw [run_bind (readBytes_run hr), pure_bind, run_bind (readNat_run hu)]
  rfl

theorem forIn_cons_run {β} {a : Nat} {l : List Nat} {init b : β} {G : Nat → β → Parser (ForInStep β)}
    {s s1 : Bytes} (h : G a init s = .ok (.yield b, s1)) :
    (forIn (a :: l) init G : Parser β) s = (forIn l b G : Parser β) s1 := by
  rw [List.forIn_cons, run_bind h]

/-- The child loop of `readChildren`, abstractly. -/
theorem children_loop (P : Nat → Bool) (G : Nat → List (Nat × Hash) → Parser (ForInStep (List (Nat × Hash))))
    (hG1 : ∀ n acc (b rest : Bytes), P n = true → b.length = 32 →
      G n acc (b ++ rest) = .ok (.yield (acc ++ [(n, b)]), rest))
    (hG0 : ∀ n acc s, P n = false → G n acc s = .ok (.yield acc, s)) :
    ∀ (l : List Nat) (cs : List (Nat × Hash)) acc rest, cs.map (·.1) = l.filter P →
      (∀ c ∈ cs, c.2.length = 32) →
      (forIn l acc G : Parser _) ((cs.map (·.2)).flatten ++ rest) = .ok (acc ++ cs, rest) := by
  intro l
  induction l with
  | nil =>
    intro cs acc rest hk _
    have : cs = [] := by simpa using hk
    subst this
    simp only [List.map_nil, List.flatten_nil, List.nil_append, List.append_nil]
    rfl
  | cons n l ih =>
    intro cs acc rest hk hl
    cases hP : P n with
    | false =>
      rw [forIn_cons_run (hG0 _ _ _ hP)]
      exact ih cs acc rest (by simpa [List.filter_cons, hP] using hk) hl
    | true =>
      rw [List.filter_cons, hP] at hk
      obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
        cases cs with
        | nil => simp at hk
        | cons c cs' => exact ⟨c, cs', rfl⟩
      simp only [↓reduceIte, List.map_cons, List.cons.injEq] at hk
      obtain ⟨c1, c2⟩ := c
      simp only at hk
      obtain ⟨rfl, hk⟩ := hk
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      rw [forIn_cons_run (hG1 c1 acc c2 _ hP (hl (c1, c2) (by simp))), ih cs' _ rest hk
        (fun c hc => hl c (by simp [hc]))]
      simp

/-- `m` is the child mask of the predicate `P` below nibble `i`. -/
def Bits (P : Nat → Bool) (m i : Nat) : Prop :=
  m < 2 ^ i ∧ ∀ j < i, m / 2 ^ j % 2 = if P j then 1 else 0

theorem Bits.zero (P : Nat → Bool) : Bits P 0 0 := ⟨by simp, fun j hj => absurd hj (by omega)⟩

theorem Bits.step {P : Nat → Bool} {m i : Nat} (h : Bits P m i) :
    Bits P (if P i then m + 2 ^ i else m) (i + 1) := by
  obtain ⟨hlt, hb⟩ := h
  have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
  cases hP : P i with
  | false =>
    refine ⟨by simp only [Bool.false_eq_true, ↓reduceIte]; omega, fun j hj => ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hb j hj
    · rw [Nat.div_eq_of_lt hlt, hP]; rfl
  | true =>
    simp only [↓reduceIte]
    refine ⟨by omega, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have he : 2 ^ i = 2 ^ j * (2 * 2 ^ (i - j - 1)) := by
        rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
      rw [he, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.add_mul_mod_self_left]
      exact hb j hj
    · rw [hP]
      have : (m + 2 ^ j) / 2 ^ j = 1 := by
        rw [Nat.add_div_right _ (Nat.two_pow_pos j), Nat.div_eq_of_lt hlt]
      simp [this]

theorem readChildren_run {P : Nat → Bool} {M : Nat} {cs : List (Nat × Hash)} {rest : Bytes}
    (hM : Bits P M 16) (hk : cs.map (·.1) = (List.range' 0 16).filter P)
    (hl : ∀ c ∈ cs, c.2.length = 32) :
    readChildren (little 2 M ++ ((cs.map (·.2)).flatten ++ rest)) = .ok (cs, rest) := by
  unfold readChildren
  rw [run_bind (readNat_run hM.1)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind_pure]
  have hk' : cs.map (·.1) = (List.range' 0 16).filter (fun n => M / 2 ^ n % 2 == 1) := by
    rw [hk]
    apply List.filter_congr
    intro n hn
    have hn16 : n < 16 := by simp at hn; omega
    rw [hM.2 n hn16]
    cases P n <;> rfl
  have e16 : [:16].size = 16 := rfl
  rw [e16]
  refine Eq.trans (children_loop (fun n => M / 2 ^ n % 2 == 1) _ ?_ ?_ (List.range' 0 16) cs [] rest
    hk' hl) (by rw [List.nil_append])
  · intro n acc b rest hP hb
    simp only [hP, ↓reduceIte]
    rw [run_bind (readBytes_run hb)]
    rfl
  · intro n acc s hP
    simp only [hP, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem decodeNode_branch_none {P : Nat → Bool} {M u : Nat} {cs : List (Nat × Hash)}
    (hM : Bits P M 16) (hk : cs.map (·.1) = (List.range' 0 16).filter P)
    (hl : ∀ c ∈ cs, c.2.length = 32) (hu : u < 2 ^ 64) :
    decodeNode ([1] ++ little 2 M ++ (cs.map (·.2)).flatten ++ little 8 u) =
      .ok (.branch none cs) := by
  unfold decodeNode
  refine decode_of_run ?_
  have e : [1] ++ little 2 M ++ (cs.map (·.2)).flatten ++ little 8 u =
      little 1 1 ++ (little 2 M ++ ((cs.map (·.2)).flatten ++ (little 8 u ++ []))) := by
    simp only [List.append_assoc, List.append_nil]; rfl
  rw [e, run_bind (readNat_run (by decide))]
  show (do
    let node ← pure (Node.branch none (← readChildren))
    let _ ← readNat 8
    pure node : Parser Node) _ = _
  rw [run_bind (readChildren_run hM hk hl), pure_bind, run_bind (readNat_run hu)]
  rfl

theorem decodeNode_branch_some {P : Nat → Bool} {M u : Nat} {cs : List (Nat × Hash)} {v : Bytes}
    (hv : v.length < 2 ^ 32)
    (hM : Bits P M 16) (hk : cs.map (·.1) = (List.range' 0 16).filter P)
    (hl : ∀ c ∈ cs, c.2.length = 32) (hu : u < 2 ^ 64) :
    decodeNode ([2] ++ refBytes v ++ little 2 M ++ (cs.map (·.2)).flatten ++ little 8 u) =
      .ok (.branch (some (refOf v)) cs) := by
  unfold decodeNode
  refine decode_of_run ?_
  have e : [2] ++ refBytes v ++ little 2 M ++ (cs.map (·.2)).flatten ++ little 8 u =
      little 1 2 ++ (refBytes v ++ (little 2 M ++ ((cs.map (·.2)).flatten ++ (little 8 u ++ [])))) := by
    simp only [List.append_assoc, List.append_nil]; rfl
  rw [e, run_bind (readNat_run (by decide))]
  show (do
    let value ← readRef
    let node ← pure (Node.branch (some value) (← readChildren))
    let _ ← readNat 8
    pure node : Parser Node) _ = _
  rw [run_bind (readRef_run hv), run_bind (readChildren_run hM hk hl), pure_bind,
    run_bind (readNat_run hu)]
  rfl

abbrev Acc := Nat × Bytes × Witness × Nat

/-- The construction's child loop, abstractly: every present nibble's child
is built and accumulated, absent nibbles are skipped. -/
theorem build_loop (P : Nat → Bool) (Ch : Nat → Built → Prop)
    (F : Nat → Acc → Except String (ForInStep Acc))
    (hF1 : ∀ n s r, P n = true → F n s = .ok r → ∃ C, Ch n C ∧
      r = .yield (s.1 + 2 ^ n, s.2.1 ++ C.root, s.2.2.1 ++ C.witness, s.2.2.2 + C.memoryUsage))
    (hF0 : ∀ n s, P n = false → F n s = .ok (.yield s)) :
    ∀ k i (init R : Acc), forIn (List.range' i k) init F = .ok R → Bits P init.1 i →
      Bits P R.1 (i + k) ∧ ∃ cs : List (Nat × Built), cs.map (·.1) = (List.range' i k).filter P ∧
        (∀ c ∈ cs, Ch c.1 c.2) ∧ R.2.1 = init.2.1 ++ (cs.map (·.2.root)).flatten ∧
        R.2.2.1 = init.2.2.1 ++ (cs.map (·.2.witness)).flatten ∧
        R.2.2.2 = init.2.2.2 + (cs.map (·.2.memoryUsage)).sum := by
  intro k
  induction k with
  | zero =>
    intro i init R h hb
    simp only [List.range'_zero, List.forIn_nil] at h
    cases h
    exact ⟨hb, [], by simp, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    intro i init R h hb
    rw [List.range'_succ, List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i r hr
    cases hP : P i with
    | false =>
      rw [hF0 _ _ hP] at hr
      cases hr
      have hb' := hb.step (P := P)
      simp only [hP, Bool.false_eq_true, ↓reduceIte] at hb'
      obtain ⟨h1, cs, hk, hc, h2, h3, h4⟩ := ih (i + 1) init R h hb'
      refine ⟨by rwa [Nat.add_assoc, Nat.add_comm 1 k] at h1, cs, ?_, hc, h2, h3, h4⟩
      rw [List.range'_succ, List.filter_cons, hP]
      simpa using hk
    | true =>
      obtain ⟨C, hC, rfl⟩ := hF1 _ _ _ hP hr
      have hb' := hb.step (P := P)
      simp only [hP, ↓reduceIte] at hb'
      obtain ⟨h1, cs, hk, hc, h2, h3, h4⟩ := ih (i + 1) _ R h hb'
      refine ⟨by rwa [Nat.add_assoc, Nat.add_comm 1 k] at h1, (i, C) :: cs, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.range'_succ, List.filter_cons, hP]
        simp [hk]
      · intro c hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact hC
        · exact hc c hc'
      · rw [h2]; simp
      · rw [h3]; simp
      · rw [h4]; simp; omega

/-! ## Construction represents its entries -/

/-- The map a list of nibble-path entries denotes: the first binding wins,
as in the host's `storage` function. -/
def sem (E : List (List Nat × Bytes)) (p : List Nat) : Option Bytes :=
  (E.find? (·.1 == p)).map (·.2)

theorem sem_nil : sem [] = fun _ => none := rfl

theorem sem_leaf (p : List Nat) (v : Bytes) :
    sem [(p, v)] = fun k => if p = k then some v else none := by
  funext k
  unfold sem
  by_cases h : p = k <;> simp [h]

theorem sem_ext (E : List (List Nat × Bytes)) (sh : List Nat) (hE : ∀ x ∈ E, sh <+: x.1) :
    sem E = fun k => if sh.isPrefixOf k then sem (E.map fun x => (x.1.drop sh.length, x.2))
      (k.drop sh.length) else none := by
  funext k
  induction E with
  | nil => simp [sem]
  | cons x E ih =>
    have ih := ih (fun y hy => hE y (by simp [hy]))
    obtain ⟨t, ht⟩ := hE x (by simp)
    unfold sem at ih ⊢
    simp only [List.find?_cons, List.map_cons]
    by_cases hk : sh.isPrefixOf k
    · obtain ⟨tk, htk⟩ := List.isPrefixOf_iff_prefix.mp hk
      simp only [hk, ↓reduceIte] at ih ⊢
      have : (x.1 == k) = (x.1.drop sh.length == k.drop sh.length) := by
        rw [← ht, ← htk]
        simp only [List.drop_left]
        exact Bool.eq_iff_iff.mpr (by simp)
      rw [this]
      cases (List.drop sh.length x.fst == List.drop sh.length k)
      · exact ih
      · rfl
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      have : (x.1 == k) = false := by
        rw [beq_eq_false_iff_ne]; rintro rfl
        exact hk (List.isPrefixOf_iff_prefix.mpr ⟨t, ht⟩)
      simp only [this]
      exact ih

theorem sem_branch_nil (E : List (List Nat × Bytes)) :
    sem E [] = (E.find? (·.1.isEmpty)).map (·.2) := by
  unfold sem
  congr 2
  funext x
  cases x.1 <;> rfl

theorem sem_branch_cons (E : List (List Nat × Bytes)) (n : Nat) (rest : List Nat) :
    sem E (n :: rest) =
      sem ((E.filter fun e => e.1.head? == some n).map fun x => (x.1.tail, x.2)) rest := by
  induction E with
  | nil => rfl
  | cons x E ih =>
    unfold sem at ih ⊢
    obtain ⟨p, v⟩ := x
    cases p with
    | nil => simpa [List.filter_cons] using ih
    | cons a p =>
      by_cases ha : a = n
      · subst ha
        by_cases hp : p = rest
        · subst hp; simp
        · simp [hp]
          simpa using ih
      · simp [ha]
        simpa using ih

theorem common_prefix : ∀ a b : List Nat, common a b <+: a ∧ common a b <+: b
  | a :: as, b :: bs => by
    rw [common]
    split
    · rename_i h
      have hab : a = b := by simpa using h
      subst hab
      obtain ⟨h1, h2⟩ := common_prefix as bs
      exact ⟨List.prefix_cons_inj _ |>.mpr h1, List.prefix_cons_inj _ |>.mpr h2⟩
    · exact ⟨List.nil_prefix, List.nil_prefix⟩
  | [], _ => by rw [common] <;> first | exact ⟨List.nil_prefix, List.nil_prefix⟩ | simp
  | _ :: _, [] => by rw [common] <;> first | exact ⟨List.nil_prefix, List.nil_prefix⟩ | simp

theorem shared_prefix : ∀ (rest : List (List Nat × Bytes)) (init : List Nat),
    rest.foldl (fun path entry => common path entry.1) init <+: init ∧
      ∀ x ∈ rest, rest.foldl (fun path entry => common path entry.1) init <+: x.1
  | [], init => ⟨List.prefix_refl _, by simp⟩
  | y :: rest, init => by
    obtain ⟨h1, h2⟩ := shared_prefix rest (common init y.1)
    obtain ⟨c1, c2⟩ := common_prefix init y.1
    refine ⟨h1.trans c1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1.trans c2
    · exact h2 x hx

theorem finish_ok {node : Bytes} {usage : Nat} {objs : Witness} {C : Built}
    (h : finish node usage objs = .ok C) :
    usage < 2 ^ 64 ∧ C.root = Near.Sha256.hash (node ++ little 8 usage) ∧ C.memoryUsage = usage ∧
      C.witness = (C.root, node ++ little 8 usage) :: objs := by
  unfold finish at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · rename_i hh; cases hh
  · cases h
    exact ⟨by omega, rfl, rfl, rfl⟩

theorem little_inj {n u u' : Nat} (hu : u < 2 ^ (8 * n)) (hu' : u' < 2 ^ (8 * n))
    (h : little n u = little n u') : u = u' := by
  rw [← little_fold n u hu, ← little_fold n u' hu', h]

theorem mem_unique {U : Witness} (hU : (U.map Prod.fst).Nodup) {a : Hash} {b1 b2 : Bytes}
    (h1 : (a, b1) ∈ U) (h2 : (a, b2) ∈ U) : b1 = b2 := by
  have e1 := fetch_of_mem hU h1
  have e2 := fetch_of_mem hU h2
  simp only at e1 e2
  rw [e1] at e2
  cases e2; rfl

/-- `a` names a witness node object whose subtree usage exceeds `u`. -/
def Big (U : Witness) (a : Hash) (u : Nat) : Prop :=
  ∃ pre u', u < u' ∧ u' < 2 ^ 64 ∧ (a, pre ++ little 8 u') ∈ U

theorem Big.mono {U : Witness} {a : Hash} {u v : Nat} (h : Big U a u) (hv : v ≤ u) : Big U a v := by
  obtain ⟨pre, u', h1, h2, h3⟩ := h
  exact ⟨pre, u', by omega, h2, h3⟩

theorem not_anc {U : Witness} (hU : (U.map Prod.fst).Nodup) {h a : Hash} {node : Bytes} {u : Nat}
    (hm : (h, node ++ little 8 u) ∈ U) (hu : u < 2 ^ 64) (hb : Big U a u) : a ≠ h := by
  rintro rfl
  obtain ⟨pre, u', h1, h2, h3⟩ := hb
  have e := mem_unique hU hm h3
  have := List.append_inj_right' e (by rw [little_length, little_length])
  have := little_inj (n := 8) hu h2 this
  omega

theorem le_sum_of_mem' {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h; simp; omega

theorem finish_root {node : Bytes} {usage : Nat} {objs : Witness} {C : Built}
    (h : finish node usage objs = .ok C) : C.root.length = 32 := by
  rw [(finish_ok h).2.1]; exact Near.Sha256.hash_length _

theorem construct_root_len {fuel : Nat} {E : List (List Nat × Bytes)} {C : Built}
    (h : construct fuel E = .ok C) (hne : E ≠ []) : C.root.length = 32 := by
  cases fuel with
  | zero => unfold construct at h; cases h
  | succ fuel =>
    unfold construct at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact absurd rfl hne
    all_goals (repeat' split at h) <;> first | exact finish_root h | cases h | (rename_i hh; cases hh)

/-- Entries whose paths are nibble sequences and whose values fit a u32 length. -/
def Bounded (E : List (List Nat × Bytes)) : Prop :=
  ∀ x ∈ E, (∀ n ∈ x.1, n < 16) ∧ x.2.length < 2 ^ 32

theorem construct_rep (U : Witness) (hU : (U.map Prod.fst).Nodup) (hz : zeroHash ∉ U.map Prod.fst) :
    ∀ fuel (E : List (List Nat × Bytes)) (C : Built), construct fuel E = .ok C → Bounded E →
      (∀ x ∈ C.witness, x ∈ U) →
      C.memoryUsage < 2 ^ 64 ∧
      (E ≠ [] → C.root.length = 32 ∧ ∃ node, (C.root, node ++ little 8 C.memoryUsage) ∈ U) ∧
      ∀ A, (∀ a ∈ A, Big U a C.memoryUsage) → Rep U A C.root (sem E) := by
  intro fuel
  induction fuel with
  | zero => intro E C h; unfold construct at h; cases h
  | succ fuel ih =>
    intro E C h hE hW
    unfold construct at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
      refine ⟨by decide, fun h => absurd rfl h, fun A _ => ?_⟩
      rw [sem_nil]
      exact Rep.empty A
    · rename_i p v
      split at h
      · split at h
        · cases h
        · rename_i hh; cases hh
      rename_i henc
      have henc : (encodePath true p).length < 2 ^ 32 := by omega
      obtain ⟨hu, hroot, husage, hwit⟩ := finish_ok h
      have hpv := hE (p, v) (by simp)
      have hmem : (C.root, ([0] ++ vector (encodePath true p) ++ refBytes v) ++
          little 8 C.memoryUsage) ∈ U := by
        rw [husage]; exact hW _ (by rw [hwit]; simp)
      have hroot32 : C.root.length = 32 := by rw [hroot]; exact Near.Sha256.hash_length _
      rw [← husage] at hu
      refine ⟨hu, fun _ => ⟨hroot32, _, hmem⟩, fun A hA => ?_⟩
      rw [sem_leaf]
      refine Rep.leaf A C.root _ p v ?_ ?_ (fetch_of_mem hU hmem) ?_ ?_
      · intro h0; exact hz (h0 ▸ List.mem_map_of_mem hmem)
      · intro hin; exact not_anc hU hmem hu (hA _ hin) rfl
      · exact decodeNode_leaf hpv.1 henc hpv.2 hu
      · exact fetch_of_mem hU (hW (Near.Sha256.hash v, v) (by rw [hwit]; simp))
    · rename_i _ x xs _
      have hpre := shared_prefix xs x.1
      generalize hsh : List.foldl (fun path entry => common path entry.fst) x.fst xs = sh at h hpre
      have hpre' : ∀ y ∈ x :: xs, sh <+: y.1 := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hpre.1
        · exact hpre.2 y hy
      split at h
      · -- extension
        rename_i hshne
        split at h
        · cases h
        rename_i C' hC'
        split at h
        · split at h
          · cases h
          · rename_i hh; cases hh
        rename_i henc
        have henc : (encodePath false sh).length < 2 ^ 32 := by omega
        obtain ⟨hu, hroot, husage, hwit⟩ := finish_ok h
        have hB' : Bounded ((x :: xs).map fun y => (y.1.drop sh.length, y.2)) := by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
          exact ⟨fun n hn => (hE z hz).1 n (List.mem_of_mem_drop hn), (hE z hz).2⟩
        have hW' : ∀ y ∈ C'.witness, y ∈ U := fun y hy => hW y (by rw [hwit]; simp [hy])
        obtain ⟨hu', hne', hrep'⟩ := ih _ _ hC' hB' hW'
        obtain ⟨hr32, node', hmem'⟩ := hne' (by simp)
        have hmem : (C.root, ([3] ++ vector (encodePath false sh) ++ C'.root) ++
            little 8 C.memoryUsage) ∈ U := by
          rw [husage]; exact hW _ (by rw [hwit]; simp)
        have hroot32 : C.root.length = 32 := by rw [hroot]; exact Near.Sha256.hash_length _
        have hshn : ∀ n ∈ sh, n < 16 := fun n hn => (hE x (by simp)).1 n (hpre.1.subset hn)
        have hlt : C'.memoryUsage < C.memoryUsage := by rw [husage]; omega
        rw [← husage] at hu
        refine ⟨hu, fun _ => ⟨hroot32, _, hmem⟩, fun A hA => ?_⟩
        rw [sem_ext _ sh hpre']
        refine Rep.extension A C.root _ sh C'.root _ ?_ ?_ (fetch_of_mem hU hmem) ?_ ?_
        · intro h0; exact hz (h0 ▸ List.mem_map_of_mem hmem)
        · intro hin; exact not_anc hU hmem hu (hA _ hin) rfl
        · exact decodeNode_extension_run hshn (by simpa using hshne) henc hr32 hu
        · refine hrep' _ fun a ha => ?_
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨_, _, hlt, hu, hmem⟩
          · exact (hA a ha).mono (Nat.le_of_lt hlt)
      · -- branch
        generalize hEx : x :: xs = E at h hE ⊢
        split at h
        · cases h
        rename_i R hR
        simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at hR
        change forIn (List.range' 0 16) _ _ = _ at hR
        let P : Nat → Bool := fun n => !(E.filter fun entry => entry.1.head? == some n).isEmpty
        let grp : Nat → List (List Nat × Bytes) := fun n =>
          (E.filter fun entry => entry.1.head? == some n).map fun y => (y.1.tail, y.2)
        have hL := build_loop P (fun n C => construct fuel (grp n) = .ok C)
          _ ?h1 ?h0 16 0 _ R hR (Bits.zero P)
        case h1 =>
          intro n s r hP hr
          simp only [P] at hP
          simp only [hP, ↓reduceIte] at hr
          split at hr
          · cases hr
          · rename_i C hC
            cases hr
            exact ⟨C, hC, rfl⟩
        case h0 =>
          intro n s hP
          simp only [P] at hP
          simp only [hP, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hBits, cs, hk, hc, hH, hO, hUs⟩ := hL
        simp only [List.nil_append, Nat.zero_add] at hH hO hUs hBits
        let children : List (Nat × Hash) := cs.map fun c => (c.1, c.2.root)
        have hkc : children.map (·.1) = (List.range' 0 16).filter P := by
          rw [← hk]; simp [children]
        have hHc : R.2.1 = (children.map (·.2)).flatten := by
          rw [hH, List.map_map]; rfl
        have hPc : ∀ c ∈ cs, P c.1 = true := by
          intro c hc'
          have : c.1 ∈ (List.range' 0 16).filter P := hk ▸ List.mem_map_of_mem hc'
          exact (List.mem_filter.mp this).2
        have hgB : ∀ n, Bounded (grp n) := by
          intro n y hy
          obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hy
          have hzE := (List.mem_filter.mp hz').1
          exact ⟨fun m hm => (hE z hzE).1 m (List.mem_of_mem_tail hm), (hE z hzE).2⟩
        have hgne : ∀ n, P n = true → grp n ≠ [] := by
          intro n hn
          simp only [P, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hn
          simpa [grp] using hn
        -- the generic tail of the branch case, for either header
        have key : ∀ (hdr : Bytes) (usage : Nat) (objs : Witness) (val : Option Bytes),
            finish (hdr ++ little 2 R.1 ++ R.2.1) usage objs = .ok C →
            (∀ y ∈ R.2.2.1, y ∈ objs) → R.2.2.2 ≤ usage →
            val = (E.find? (·.1.isEmpty)).map (·.2) →
            (∀ v, val = some v → (Near.Sha256.hash v, v) ∈ objs) →
            (∀ u, u < 2 ^ 64 → decodeNode (hdr ++ little 2 R.1 ++ R.2.1 ++ little 8 u) =
              .ok (.branch (val.map refOf) children)) →
            C.memoryUsage < 2 ^ 64 ∧
              (E ≠ [] → C.root.length = 32 ∧ ∃ node, (C.root, node ++ little 8 C.memoryUsage) ∈ U) ∧
              ∀ A, (∀ a ∈ A, Big U a C.memoryUsage) → Rep U A C.root (sem E) := by
          intro hdr usage objs val hfin hobj husg hval hvs hdec
          obtain ⟨hu, hroot, husage, hwit⟩ := finish_ok hfin
          have hmem : (C.root, (hdr ++ little 2 R.1 ++ R.2.1) ++ little 8 C.memoryUsage) ∈ U := by
            rw [husage]; exact hW _ (by rw [hwit]; simp)
          have hroot32 : C.root.length = 32 := by rw [hroot]; exact Near.Sha256.hash_length _
          have hobjU : ∀ y ∈ objs, y ∈ U := fun y hy => hW y (by rw [hwit]; simp [hy])
          rw [← husage] at hu husg
          refine ⟨hu, fun _ => ⟨hroot32, _, hmem⟩, fun A hA => ?_⟩
          have hfun : sem E = fun k => match k with
              | [] => val
              | n :: rest => if (children.find? (·.1 == n)).isSome then sem (grp n) rest else none := by
            funext k
            cases k with
            | nil => rw [sem_branch_nil, hval]
            | cons n rest =>
              rw [sem_branch_cons]
              dsimp only
              split
              · rfl
              · rename_i hnone
                have hg : grp n = [] := by
                  apply Classical.byContradiction
                  intro hne
                  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
                  obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hy
                  have hzf := List.mem_filter.mp hz'
                  have hhead : z.1.head? = some n := by simpa using hzf.2
                  have hn16 : n < 16 :=
                    (hE z hzf.1).1 n (List.mem_of_mem_head? (l := z.1) (by rw [hhead]; rfl))
                  have hPn : P n = true := by
                    simp only [P, Bool.not_eq_true', List.isEmpty_eq_false_iff]
                    exact List.ne_nil_of_mem hz'
                  have hmem : n ∈ children.map (·.1) := by
                    rw [hkc]; exact List.mem_filter.mpr ⟨List.mem_range'_1.mpr ⟨by omega, by omega⟩, hPn⟩
                  obtain ⟨c, hc', hc1⟩ := List.mem_map.mp hmem
                  apply hnone
                  exact List.find?_isSome.mpr ⟨c, hc', by simp [hc1]⟩
                show sem (grp n) rest = none
                rw [hg]; rfl
          rw [hfun]
          refine Rep.branch A C.root _ val children (fun n => sem (grp n)) ?_ ?_ (fetch_of_mem hU hmem)
            (hdec _ hu) ?_ ?_
          · intro h0; exact hz (h0 ▸ List.mem_map_of_mem hmem)
          · intro hin; exact not_anc hU hmem hu (hA _ hin) rfl
          · intro v hv; exact fetch_of_mem hU (hobjU _ (hvs v hv))
          · intro n p hp
            have hpm := List.mem_of_find?_eq_some hp
            have hpn : p.1 = n := by simpa using List.find?_some hp
            obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hpm
            simp only at hpn
            subst hpn
            have hcW : ∀ y ∈ c.2.witness, y ∈ U := by
              intro y hy
              refine hobjU y (hobj y ?_)
              rw [hO]
              exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hc', hy⟩
            obtain ⟨-, -, hrep⟩ := ih _ _ (hc c hc') (hgB _) hcW
            have hlt : c.2.memoryUsage < C.memoryUsage := by
              have := le_sum_of_mem' (List.mem_map_of_mem (f := fun x : Nat × Built => x.2.memoryUsage) hc')
              omega
            refine hrep _ fun a ha => ?_
            rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨_, _, hlt, hu, hmem⟩
            · exact (hA a ha).mono (Nat.le_of_lt hlt)
        have hch32 : ∀ c ∈ children, c.2.length = 32 := by
          intro c hc'
          obtain ⟨c', hc'', rfl⟩ := List.mem_map.mp hc'
          exact construct_root_len (hc c' hc'') (hgne _ (hPc c' hc''))
        split at h
        · rename_i v hv
          have hvE : v.length < 2 ^ 32 := by
            obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hv
            exact (hE y (List.mem_of_find?_eq_some hy)).2
          refine key ([2] ++ refBytes v) _ _ (some v) h (fun y hy => by simp [hy]) (by omega) hv.symm
            (fun w hw => by cases hw; simp) (fun u hu => ?_)
          rw [hHc]
          exact decodeNode_branch_some hvE hBits hkc hch32 hu
        · rename_i hv
          refine key [1] _ _ none h (fun y hy => hy) (Nat.le_refl _) ?_ (fun w hw => by cases hw)
            (fun u hu => ?_)
          · cases hfv : (E.find? (·.1.isEmpty)).map (·.2) with
            | none => rfl
            | some w => exact absurd hfv (hv w)
          · rw [hHc]
            exact decodeNode_branch_none hBits hkc hch32 hu

/-! ## The storage lookup phase over a canonical base -/

theorem nibbles_bound (k : Bytes) : ∀ n ∈ nibbles k, n < 16 := by
  induction k with
  | nil => simp [nibbles]
  | cons x k ih =>
    intro n hn
    rw [nibbles_cons] at hn
    have := x.toNat_lt
    rcases List.mem_cons.mp hn with rfl | hn
    · omega
    rcases List.mem_cons.mp hn with rfl | hn
    · omega
    · exact ih n hn

theorem nibbles_inj : ∀ {a b : Bytes}, nibbles a = nibbles b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [nibbles] at h
  | _ :: _, [], h => by simp [nibbles] at h
  | x :: a, y :: b, h => by
    rw [nibbles_cons, nibbles_cons] at h
    simp only [List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have : x.toNat = y.toNat := by omega
    rw [UInt8.toNat_inj.mp this, nibbles_inj h3]

theorem sem_nibbles (e : List (Bytes × Bytes)) (k : Bytes) :
    sem (e.map fun x => (nibbles x.1, x.2)) (nibbles k) = (e.find? (·.1 == k)).map (·.2) := by
  induction e with
  | nil => rfl
  | cons x e ih =>
    unfold sem at ih ⊢
    have : (nibbles x.1 == nibbles k) = (x.1 == k) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact ⟨nibbles_inj, fun h => h ▸ rfl⟩
    simp only [List.map_cons, List.find?_cons, this]
    cases (x.1 == k)
    · exact ih
    · rfl

/-- **Lookup after build.** A canonical base represents its entries: walking
from the root finds exactly the first binding of each key. The only
assumption is that no witness object hashes to the all-zero empty-trie
sentinel. -/
theorem build_rep {e : List (Bytes × Bytes)} {B : Built} (h : build e = .ok B)
    (hz : zeroHash ∉ B.witness.map Prod.fst) :
    Rep B.witness [] B.root (sem (e.map fun x => (nibbles x.1, x.2))) := by
  obtain ⟨hbd, fuel, C, hC, hroot, -, hnd, hsub⟩ := build_spec h
  have hB : Bounded (e.map fun x => (nibbles x.1, x.2)) := by
    intro y hy
    obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hy
    exact ⟨nibbles_bound _, (hbd z hz').2⟩
  rw [hroot]
  exact (construct_rep B.witness hnd hz fuel _ C hC hB hsub).2.2 [] (by simp)

/-- The per-counter form of `getReference_cost`, as `prepareStorageCallAux`
charges them (`touching_trie_node` for `disk`, `read_cached_trie_node` for
`mem`): both counters only grow, by at most `2·|k| + 1` together. -/
theorem getReference_counters {s s' : State} {k : Bytes} {b : Bool} {p : Option ValuePointer}
    (h : getReference s k b = .ok (s', p)) :
    ∃ d m, s'.accounting.disk = s.accounting.disk + d ∧ s'.accounting.mem = s.accounting.mem + m ∧
      d + m ≤ 2 * k.length + 1 := by
  obtain ⟨-, hc, -⟩ := getReference_cost h
  unfold getReference at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; exact ⟨0, 0, rfl, rfl, by omega⟩
  · cases h; exact ⟨0, 0, rfl, rfl, by omega⟩
  · split at h
    · cases h
    · cases h
      refine ⟨_, _, rfl, rfl, ?_⟩
      simp only [cost] at hc
      omega

/-- The per-counter form of `dereference_cost'` for an on-disk pointer: one
access, fresh (`disk`) or cached (`mem`). -/
theorem dereference_counters {s s' : State} {root : Hash} {r : ValueRef} {v : Bytes}
    (h : Near.TrieOverlay.dereference s (.trie root r) = .ok (s', v)) :
    ∃ d m, s'.accounting.disk = s.accounting.disk + d ∧ s'.accounting.mem = s.accounting.mem + m ∧
      d + m = 1 := by
  unfold Near.TrieOverlay.dereference at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · rename_i hd
      cases h
      unfold Near.TrieAccounting.dereference at hd
      simp only [bind, Except.bind, pure, Except.pure] at hd
      split at hd
      · cases hd
      · split at hd
        · split at hd
          · cases hd
          · rename_i hh; cases hh
        · cases hd
          simp only [Accounting.touch]
          split <;> exact ⟨_, _, rfl, rfl, by simp⟩
  · split at h
    · cases h
    · rename_i hh; cases hh

/-- **Storage lookup, correctness and cost.** For a state whose base is the
canonical construction of its entries, and a key the overlay does not
mention: `getReference` succeeds, its pointer is present exactly when the
key has a value in the entries (first binding, as the host's `storage`), it
adds at most `2·|k| + 1` accesses and changes only the accounting; and
dereferencing the pointer succeeds with exactly that value, adding one
access and again changing only the accounting. -/
theorem storage_lookup {s : State} {k : Bytes} (b : Bool)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hp : ∀ e ∈ s.prospective, e.1 ≠ k) (hc : ∀ e ∈ s.committed, e.1 ≠ k) :
    ∃ s', getReference s k b =
        .ok (s', ((s.entries.find? (·.1 == k)).map (·.2)).map fun v => .trie s.base.root (refOf v)) ∧
      SameData s s' ∧
      (∃ d m, s'.accounting.disk = s.accounting.disk + d ∧ s'.accounting.mem = s.accounting.mem + m ∧
        d + m ≤ 2 * k.length + 1) ∧
      (b = false → cost s'.accounting = cost s.accounting) ∧
      ∀ v, (s.entries.find? (·.1 == k)).map (·.2) = some v →
        ∃ s'', Near.TrieOverlay.dereference s' (.trie s.base.root (refOf v)) = .ok (s'', v) ∧
          SameData s' s'' ∧ cost s''.accounting = cost s'.accounting + 1 := by
  have hr := build_rep hb hz
  obtain ⟨s', hget, hsd, hder⟩ := getReference_rep b hr hp hc
  rw [sem_nibbles] at hget hder
  obtain ⟨-, -, hcost0⟩ := getReference_cost hget
  exact ⟨s', hget, hsd, getReference_counters hget, hcost0, hder⟩

/-- States produced by `start` satisfy the hypotheses of `storage_lookup`
(up to the zero-hash assumption): empty overlay, canonical base. -/
theorem start_spec {entries : List (Bytes × Bytes)} {s : State} (h : start entries = .ok s) :
    s.entries = entries ∧ build s.entries = .ok s.base ∧ s.prospective = [] ∧ s.committed = [] := by
  unfold start at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i B hB
    cases h
    exact ⟨rfl, hB, rfl, rfl⟩

/-- A prospective overlay hit needs no trie access: the state is unchanged. -/
theorem getReference_prospective {s : State} {k k' : Bytes} {ov : Option Bytes} (b : Bool)
    (h : s.prospective.find? (·.1 == k) = some (k', ov)) :
    getReference s k b = .ok (s, ov.map .memory) := by
  unfold getReference overlay
  simp only [h, Option.map_some, Option.orElse_some]
  cases ov <;> rfl
end NearLogic
