import NearInterface.TrieBitmap

/-!
# The canonical constructor's branch loop

The invariant composes successful recursive child constructions one digit at a
time. It computes all four mutable accumulators, rather than assuming a
successful whole branch or a decoded node. Bitmap arithmetic then identifies
the ordered child payload accepted by the actual reader.
-/
namespace Near.TrieConstructionBranch
open TrieAccounting TrieConstruction TrieSerialization TrieBitmap

local macro "trie_builder" name:ident : term => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") name.getId.toString
  pure (Lean.mkIdent actual)
local macro "unfold_trie_builder" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))

/-- Alias of the actual recursive constructor. -/
def construct : Nat → List (List Nat × Bytes) → Except String Built := trie_builder construct

/-- Alias of the actual terminal size check/hash/object installation. -/
def finish : Bytes → Nat → Witness → Except String Built := trie_builder finish

def commonPath : List Nat → List Nat → List Nat := trie_builder common

abbrev Acc := Nat × Bytes × Witness × Nat

/-- Exact tuple loop body from the constructor, with local child action exposed. -/
def loopStep (active : Nat → Bool) (child : Nat → Except String Built)
    (digit : Nat) (acc : Acc) : Except String (ForInStep Acc) := do
  if active digit then
    let built ← child digit
    return .yield (acc.1 + 2 ^ digit, acc.2.1 ++ built.root,
      acc.2.2.1 ++ built.witness, acc.2.2.2 + built.memoryUsage)
  else return .yield acc

/-- The actual child construction requested for one head-nibble group. -/
def childAction (fuel : Nat) (entries : List (List Nat × Bytes)) (digit : Nat) : Except String Built :=
  construct fuel ((entries.filter (fun entry => entry.1.head? == some digit)).map
    fun (key, value) => (key.tail, value))

/-- The actual range loop from canonical branch construction. -/
def branchLoop (fuel : Nat) (entries : List (List Nat × Bytes)) : Except String Acc :=
  forIn [:16] (0, [], [], 50) (loopStep (groupActive entries) (childAction fuel entries))

/-- Generic accumulator invariant. The digit list may have any length; only
selected child actions need to succeed. Ascending unique digits are supplied
by the constructor's range when obtaining bitmap semantics. -/
theorem loop_contract (active : Nat → Bool) (action : Nat → Except String Built)
    (child : Nat → Built) (digits : List Nat) (acc : Acc)
    (hchild : ∀ digit ∈ digits, active digit = true → action digit = .ok (child digit)) :
    forIn digits acc (loopStep active action) = .ok
      (acc.1 + (digits.map (fun digit => if active digit then 2 ^ digit else 0)).sum,
       acc.2.1 ++ ((digits.filter active).flatMap fun digit => (child digit).root),
       acc.2.2.1 ++ ((digits.filter active).flatMap fun digit => (child digit).witness),
       acc.2.2.2 + ((digits.filter active).map fun digit => (child digit).memoryUsage).sum) := by
  induction digits generalizing acc with
  | nil => simp [List.forIn_nil, pure, Except.pure]
  | cons digit digits ih =>
    have ht : ∀ i ∈ digits, active i = true → action i = .ok (child i) :=
      fun i hi => hchild i (List.mem_cons_of_mem _ hi)
    cases hp : active digit
    · simpa [List.forIn_cons, loopStep, hp, bind, Except.bind, pure, Except.pure] using ih acc ht
    · rw [List.forIn_cons]
      simp only [loopStep, hp, ↓reduceIte, hchild digit List.mem_cons_self hp,
        bind, Except.bind, pure, Except.pure]
      rw [ih _ ht]
      simp [hp, List.append_assoc, Nat.add_assoc]

/-- Successful local child equations determine the constructor's complete
bitmap, root payload, witness concatenation and usage sum. -/
theorem branchLoop_contract (fuel : Nat) (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (hchild : ∀ digit ∈ List.range 16, groupActive entries digit = true →
      childAction fuel entries digit = .ok (child digit)) :
    branchLoop fuel entries = .ok
      (maskOf (groupActive entries) 16,
       ((List.range 16).filter (groupActive entries)).flatMap (fun digit => (child digit).root),
       ((List.range 16).filter (groupActive entries)).flatMap (fun digit => (child digit).witness),
       50 + (((List.range 16).filter (groupActive entries)).map fun digit => (child digit).memoryUsage).sum) := by
  unfold branchLoop
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  change forIn (List.range' 0 16) (0, [], [], 50) _ = _
  rw [← List.range_eq_range']
  simpa [maskOf] using loop_contract (groupActive entries) (childAction fuel entries) child
    (List.range 16) (0, [], [], 50) hchild

/-- Exact actual-constructor branch equation, before any child result is
assumed. At least two entries and empty common prefix select this branch. -/
theorem construct_branch (fuel : Nat) (first second : List Nat × Bytes)
    (rest : List (List Nat × Bytes))
    (hshared : (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 = []) :
    construct (fuel + 1) (first :: second :: rest) = (do
      let acc ← branchLoop fuel (first :: second :: rest)
      match ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd with
      | none => finish ([1] ++ littleEndian 2 acc.1 ++ acc.2.1) acc.2.2.2 acc.2.2.1
      | some value =>
        finish ([2] ++ valueRefBytes value ++ littleEndian 2 acc.1 ++ acc.2.1)
          (acc.2.2.2 + 50 + value.length) ((Sha256.hash value, value) :: acc.2.2.1)) := by
  unfold commonPath at hshared
  unfold construct
  unfold_trie_builder construct
  simp only [hshared, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold branchLoop
  congr 1
  funext acc
  cases hv : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd <;> rfl

/-- Exact finish behavior; no nonzero-root or injectivity claim is made. -/
theorem finish_parts (node : Bytes) (usage : Nat) (objects : Witness) (hroom : usage < 2 ^ 64) :
    finish node usage objects = .ok {
      root := Sha256.hash (node ++ littleEndian 8 usage), memoryUsage := usage,
      witness := (Sha256.hash (node ++ littleEndian 8 usage), node ++ littleEndian 8 usage) :: objects } := by
  unfold finish
  unfold_trie_builder finish
  simp only [Nat.not_le_of_gt hroom, ↓reduceIte, pure, Except.pure]
  rfl

/-- Actual constructor output and decoder agree for a branch without a value.
The premises concern individual child constructions and serialization widths. -/
theorem construct_branch_no_value (fuel : Nat) (first second : List Nat × Bytes)
    (rest : List (List Nat × Bytes)) (child : Nat → Built)
    (hshared : (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 = [])
    (hvalue : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd = none)
    (hchild : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      childAction fuel (first :: second :: rest) digit = .ok (child digit))
    (hwidth : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      (child digit).root.length = 32)
    (husage : 50 + ((((List.range 16).filter (groupActive (first :: second :: rest))).map
      fun digit => (child digit).memoryUsage).sum) < 2 ^ 64) :
    let active := groupActive (first :: second :: rest)
    let selected := (List.range 16).filter active
    let usage := 50 + (selected.map fun digit => (child digit).memoryUsage).sum
    let node := [1] ++ littleEndian 2 (maskOf active 16) ++ selected.flatMap (fun digit => (child digit).root)
    let bytes := node ++ littleEndian 8 usage
    construct (fuel + 1) (first :: second :: rest) = .ok {
      root := Sha256.hash bytes, memoryUsage := usage,
      witness := (Sha256.hash bytes, bytes) :: selected.flatMap (fun digit => (child digit).witness) } ∧
    decodeNode bytes = .ok (.branch none (selected.map fun digit => (digit, (child digit).root))) := by
  dsimp only
  constructor
  · rw [construct_branch fuel first second rest hshared,
      branchLoop_contract fuel (first :: second :: rest) child hchild]
    simp only [bind, Except.bind, hvalue]
    exact finish_parts _ _ _ husage
  · exact decodeNode_active_branch _ (fun digit => (child digit).root) _ hwidth husage

/-- The value-bearing branch includes its own reference, value object and
additional node/value usage, before the terminal u64 size check. -/
theorem construct_branch_value (fuel : Nat) (first second : List Nat × Bytes)
    (rest : List (List Nat × Bytes)) (child : Nat → Built) (value : Bytes)
    (hshared : (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 = [])
    (hvalue : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd = some value)
    (hchild : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      childAction fuel (first :: second :: rest) digit = .ok (child digit))
    (hwidth : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      (child digit).root.length = 32)
    (hvalueRoom : value.length < 2 ^ 32)
    (husage : 50 + ((((List.range 16).filter (groupActive (first :: second :: rest))).map
      fun digit => (child digit).memoryUsage).sum) + 50 + value.length < 2 ^ 64) :
    let active := groupActive (first :: second :: rest)
    let selected := (List.range 16).filter active
    let usage := 50 + (selected.map fun digit => (child digit).memoryUsage).sum + 50 + value.length
    let node := [2] ++ valueRefBytes value ++ littleEndian 2 (maskOf active 16) ++
      selected.flatMap (fun digit => (child digit).root)
    let bytes := node ++ littleEndian 8 usage
    construct (fuel + 1) (first :: second :: rest) = .ok {
      root := Sha256.hash bytes, memoryUsage := usage,
      witness := (Sha256.hash bytes, bytes) :: (Sha256.hash value, value) ::
        selected.flatMap (fun digit => (child digit).witness) } ∧
    decodeNode bytes = .ok (.branch (some { length := value.length, hash := Sha256.hash value })
      (selected.map fun digit => (digit, (child digit).root))) := by
  dsimp only
  constructor
  · rw [construct_branch fuel first second rest hshared,
      branchLoop_contract fuel (first :: second :: rest) child hchild]
    simp only [bind, Except.bind, hvalue]
    exact finish_parts _ _ _ husage
  · exact decodeNode_active_branch_value value _ (fun digit => (child digit).root) _ hvalueRoom hwidth husage

end Near.TrieConstructionBranch
