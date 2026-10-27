import NearInterface.TrieSerialization
import Init.Data.Range.Lemmas

/-!
# Branch child bitmap parsing

The loop contract uses an ordered digit list and the mask's actual bit test.
It is proved by list induction, without enumerating the 65536 masks.
-/
namespace Near.TrieBranch
open TrieAccounting TrieConstruction TrieSerialization

local macro "trie_parser" name:ident : term => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  pure (Lean.mkIdent actual)
local macro "unfold_trie_parser" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))
local macro "unfold_little" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "little"
  `(tactic| unfold $(Lean.mkIdent actual))

/-- Alias of the actual private child parser. -/
def takeChildren : Parser (List (Nat × Hash)) := trie_parser readChildren

/-- The exact loop body from `readChildren`, factored for its invariant. -/
def childStep (mask nibble : Nat) (children : List (Nat × Hash)) : Parser (ForInStep (List (Nat × Hash))) := do
  if mask / 2 ^ nibble % 2 == 1 then
    return .yield (children ++ [(nibble, ← takeBytes 32)])
  else return .yield children

/-- Children in the order dictated by the bitmap scan. -/
def selectedChildren (mask : Nat) (hash : Nat → Hash) (digits : List Nat) : List (Nat × Hash) :=
  (digits.filter fun nibble => mask / 2 ^ nibble % 2 == 1).map fun nibble => (nibble, hash nibble)

def childPayload (mask : Nat) (hash : Nat → Hash) (digits : List Nat) : Bytes :=
  (digits.filter fun nibble => mask / 2 ^ nibble % 2 == 1).flatMap hash

/-- Every successful child read consumes exactly 32 bytes and frames suffix;
the invariant allows any already accumulated child list. -/
theorem children_loop (mask : Nat) (hash : Nat → Hash) (digits : List Nat)
    (acc : List (Nat × Hash)) (suffix : Bytes)
    (hwidth : ∀ nibble ∈ digits, mask / 2 ^ nibble % 2 = 1 → (hash nibble).length = 32) :
    (forIn digits acc (childStep mask)).run (childPayload mask hash digits ++ suffix) =
      .ok (acc ++ selectedChildren mask hash digits, suffix) := by
  induction digits generalizing acc with
  | nil => simp [childPayload, selectedChildren, List.forIn_nil, pure, StateT.pure, StateT.run, Except.pure]
  | cons nibble digits ih =>
    have ht : ∀ n ∈ digits, mask / 2 ^ n % 2 = 1 → (hash n).length = 32 :=
      fun n hn => hwidth n (List.mem_cons_of_mem _ hn)
    by_cases hb : mask / 2 ^ nibble % 2 = 1
    · have hp := takeBytes_append (hash nibble) (childPayload mask hash digits ++ suffix)
      rw [hwidth nibble List.mem_cons_self hb] at hp
      simp only [childPayload, List.filter_cons, beq_iff_eq, hb, ↓reduceIte,
        List.flatMap_cons, List.append_assoc, List.forIn_cons, childStep,
        StateT.run, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
      simp only [childPayload, StateT.run] at hp
      rw [hp]
      dsimp only
      have hi := ih (acc ++ [(nibble, hash nibble)]) ht
      simp only [StateT.run, childPayload] at hi
      rw [hi]
      simp [selectedChildren, hb, List.append_assoc]
    · simp only [childPayload, List.filter_cons, beq_iff_eq, hb, ↓reduceIte,
        List.forIn_cons, childStep, StateT.run, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
      simpa [StateT.run, childPayload, selectedChildren, hb] using ih acc ht

theorem takeNat_little2 (value : Nat) (suffix : Bytes) (hvalue : value < 2 ^ 16) :
    (takeNat 2).run (littleEndian 2 value ++ suffix) = .ok (value, suffix) := by
  have hv : (littleEndian 2 value).foldr (fun byte rest => byte.toNat + 256 * rest) 0 = value := by
    unfold littleEndian
    unfold_little
    simp [List.range_succ]
    omega
  have h := takeNat_append (littleEndian 2 value) suffix
  rw [littleEndian_length, hv] at h
  exact h

/-- The parser's actual fixed bitmap scan is the generic list loop. -/
theorem takeChildren_run (bytes : Bytes) :
    takeChildren.run bytes = match (takeNat 2).run bytes with
    | .error e => .error e
    | .ok (mask, rest) => (forIn (List.range 16) [] (childStep mask)).run rest := by
  unfold takeChildren
  unfold_trie_parser readChildren
  simp only [takeNat, StateT.run, bind, StateT.bind, Std.Legacy.Range.forIn_eq_forIn_range']
  cases hn : ((trie_parser readNat) 2) bytes with
  | error e => simp [Except.bind]
  | ok pair =>
    obtain ⟨mask, rest⟩ := pair
    simp only [Except.bind]
    change ((forIn (List.range' 0 16) [] (childStep mask)) >>= pure) rest =
      (forIn (List.range 16) [] (childStep mask)) rest
    rw [← List.range_eq_range']
    simp only [bind_pure]

/-- A bounded u16 bitmap followed by its ordered 32-byte child payload decodes
without consuming the framed suffix. Unselected hashes need no width premise. -/
theorem takeChildren_encoded (mask : Nat) (hash : Nat → Hash) (suffix : Bytes)
    (hmask : mask < 2 ^ 16)
    (hwidth : ∀ nibble ∈ List.range 16, mask / 2 ^ nibble % 2 = 1 → (hash nibble).length = 32) :
    takeChildren.run (littleEndian 2 mask ++ childPayload mask hash (List.range 16) ++ suffix) =
      .ok (selectedChildren mask hash (List.range 16), suffix) := by
  rw [takeChildren_run, List.append_assoc, takeNat_little2 _ _ hmask]
  exact children_loop mask hash (List.range 16) [] suffix hwidth

/-- Actual tag-1 branch decoding, composed from individual field reads. -/
theorem decodeNode_branch_of_reads (bytes afterTag afterChildren : Bytes)
    (children : List (Nat × Hash)) (usage : Nat)
    (htag : (takeNat 1).run bytes = .ok (1, afterTag))
    (hchildren : takeChildren.run afterTag = .ok (children, afterChildren))
    (husage : (takeNat 8).run afterChildren = .ok (usage, [])) :
    decodeNode bytes = .ok (.branch none children) := by
  simp only [takeNat, takeChildren, StateT.run] at htag hchildren husage
  simp only [decodeNode, StateT.run, bind, StateT.bind]
  rw [htag]
  simp only [bind, Except.bind, StateT.bind, pure, StateT.pure, Except.pure]
  rw [hchildren]
  simp only []
  rw [husage]
  rfl

/-- Actual tag-2 branch decoding with a value reference before the bitmap. -/
theorem decodeNode_branch_value_of_reads (bytes afterTag afterRef afterChildren : Bytes)
    (reference : ValueRef) (children : List (Nat × Hash)) (usage : Nat)
    (htag : (takeNat 1).run bytes = .ok (2, afterTag))
    (href : takeRef.run afterTag = .ok (reference, afterRef))
    (hchildren : takeChildren.run afterRef = .ok (children, afterChildren))
    (husage : (takeNat 8).run afterChildren = .ok (usage, [])) :
    decodeNode bytes = .ok (.branch (some reference) children) := by
  simp only [takeNat, takeRef, takeChildren, StateT.run] at htag href hchildren husage
  simp only [decodeNode, StateT.run, bind, StateT.bind]
  rw [htag]
  simp only [bind, Except.bind, StateT.bind, pure, StateT.pure, Except.pure]
  rw [href]
  simp only []
  rw [hchildren]
  simp only []
  rw [husage]
  rfl

/-- A branch without a value, with arbitrary bounded bitmap and ordered child
payload, round-trips through the actual decoder. -/
theorem decodeNode_branch (mask : Nat) (hash : Nat → Hash) (usage : Nat)
    (hmask : mask < 2 ^ 16)
    (hwidth : ∀ nibble ∈ List.range 16, mask / 2 ^ nibble % 2 = 1 → (hash nibble).length = 32)
    (husage : usage < 2 ^ 64) :
    decodeNode ([1] ++ littleEndian 2 mask ++ childPayload mask hash (List.range 16) ++ littleEndian 8 usage) =
      .ok (.branch none (selectedChildren mask hash (List.range 16))) := by
  apply decodeNode_branch_of_reads _
    (littleEndian 2 mask ++ (childPayload mask hash (List.range 16) ++ littleEndian 8 usage))
    (littleEndian 8 usage) _ usage
  · simpa [List.append_assoc] using takeNat_append [1]
      (littleEndian 2 mask ++ (childPayload mask hash (List.range 16) ++ littleEndian 8 usage))
  · simpa only [List.append_assoc] using takeChildren_encoded mask hash (littleEndian 8 usage) hmask hwidth
  · simpa using takeNat_little8 usage [] husage

/-- A branch containing a value reference additionally requires its u32 value
length; the value's SHA256 encoder already guarantees its 32-byte hash. -/
theorem decodeNode_branch_value (value : Bytes) (mask : Nat) (hash : Nat → Hash) (usage : Nat)
    (hvalue : value.length < 2 ^ 32) (hmask : mask < 2 ^ 16)
    (hwidth : ∀ nibble ∈ List.range 16, mask / 2 ^ nibble % 2 = 1 → (hash nibble).length = 32)
    (husage : usage < 2 ^ 64) :
    decodeNode ([2] ++ valueRefBytes value ++ littleEndian 2 mask ++
      childPayload mask hash (List.range 16) ++ littleEndian 8 usage) =
      .ok (.branch (some { length := value.length, hash := Sha256.hash value })
        (selectedChildren mask hash (List.range 16))) := by
  apply decodeNode_branch_value_of_reads _
    (valueRefBytes value ++ (littleEndian 2 mask ++ (childPayload mask hash (List.range 16) ++ littleEndian 8 usage)))
    (littleEndian 2 mask ++ (childPayload mask hash (List.range 16) ++ littleEndian 8 usage))
    (littleEndian 8 usage) _ _ usage
  · simpa [List.append_assoc] using takeNat_append [2]
      (valueRefBytes value ++ (littleEndian 2 mask ++ (childPayload mask hash (List.range 16) ++ littleEndian 8 usage)))
  · exact takeRef_value value _ hvalue
  · simpa only [List.append_assoc] using takeChildren_encoded mask hash (littleEndian 8 usage) hmask hwidth
  · simpa using takeNat_little8 usage [] husage

end Near.TrieBranch
