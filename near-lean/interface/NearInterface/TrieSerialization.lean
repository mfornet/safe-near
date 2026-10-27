import NearInterface.TrieEncoding

/-!
# Actual trie-node serialization prerequisites

Widths and path validity are explicit. The helpers below alias the runtime's
existing transparent private encoders and parsers; no implementation is copied.
-/
namespace Near.TrieSerialization
open TrieAccounting TrieConstruction

local macro "trie_builder" name:ident : term => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") name.getId.toString
  pure (Lean.mkIdent actual)

local macro "trie_parser" name:ident : term => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  pure (Lean.mkIdent actual)

local macro "unfold_trie_builder" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))

local macro "unfold_trie_parser" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))

def littleEndian : Nat → Nat → Bytes := trie_builder little
def vectorBytes : Bytes → Bytes := trie_builder vector
def valueRefBytes : Bytes → Bytes := trie_builder refBytes
def takeBytes : Nat → Parser Bytes := trie_parser readBytes
def takeNat : Nat → Parser Nat := trie_parser readNat
def takeRef : Parser ValueRef := trie_parser readRef
def takePath : Bool → Parser (List Nat) := trie_parser readPath

@[simp] theorem littleEndian_length (count value : Nat) :
    (littleEndian count value).length = count := by
  unfold littleEndian
  unfold_trie_builder little
  simp

theorem takeBytes_run (count : Nat) (bytes : Bytes) :
    (takeBytes count).run bytes =
      if bytes.length < count then .error "truncated trie node"
      else .ok (bytes.take count, bytes.drop count) := by
  unfold takeBytes
  unfold_trie_parser readBytes
  by_cases h : bytes.length < count
  · simp [h]; rfl
  · simp [h]; rfl

/-- A byte reader consumes exactly its specified prefix and retains the suffix. -/
theorem takeBytes_append (bytes suffix : Bytes) :
    (takeBytes bytes.length).run (bytes ++ suffix) = .ok (bytes, suffix) := by
  rw [takeBytes_run]
  simp

/-- Natural parsing is the actual little-endian byte fold, with framing. -/
theorem takeNat_append (bytes suffix : Bytes) :
    (takeNat bytes.length).run (bytes ++ suffix) =
      .ok (bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0, suffix) := by
  have h := takeBytes_append bytes suffix
  unfold takeBytes at h
  unfold takeNat
  unfold_trie_parser readNat
  simp only [StateT.run] at *
  simp only [bind, StateT.bind]
  rw [show ((trie_parser readBytes) bytes.length) (bytes ++ suffix) = .ok (bytes, suffix) from h]
  rfl

/-- Four-byte little-endian reconstruction under the actual u32 bound. -/
theorem littleEndian_value4 (value : Nat) (hvalue : value < 2 ^ 32) :
    (littleEndian 4 value).foldr (fun byte rest => byte.toNat + 256 * rest) 0 = value := by
  unfold littleEndian
  unfold_trie_builder little
  simp [List.range_succ]
  omega

/-- Eight-byte little-endian reconstruction under the actual u64 bound. -/
theorem littleEndian_value8 (value : Nat) (hvalue : value < 2 ^ 64) :
    (littleEndian 8 value).foldr (fun byte rest => byte.toNat + 256 * rest) 0 = value := by
  unfold littleEndian
  unfold_trie_builder little
  simp [List.range_succ]
  omega

theorem takeNat_little4 (value : Nat) (suffix : Bytes) (hvalue : value < 2 ^ 32) :
    (takeNat 4).run (littleEndian 4 value ++ suffix) = .ok (value, suffix) := by
  have h := takeNat_append (littleEndian 4 value) suffix
  rw [littleEndian_length, littleEndian_value4 value hvalue] at h
  exact h

theorem takeNat_little8 (value : Nat) (suffix : Bytes) (hvalue : value < 2 ^ 64) :
    (takeNat 8).run (littleEndian 8 value ++ suffix) = .ok (value, suffix) := by
  have h := takeNat_append (littleEndian 8 value) suffix
  rw [littleEndian_length, littleEndian_value8 value hvalue] at h
  exact h

@[simp] theorem vectorBytes_eq (bytes : Bytes) :
    vectorBytes bytes = littleEndian 4 bytes.length ++ bytes := rfl

@[simp] theorem valueRefBytes_eq (bytes : Bytes) :
    valueRefBytes bytes = littleEndian 4 bytes.length ++ Sha256.hash bytes := rfl

/-- The parser's precise sequencing, exposed without changing it. -/
theorem takeRef_run (bytes : Bytes) :
    takeRef.run bytes = match (takeNat 4).run bytes with
      | .error e => .error e
      | .ok (length, rest) => match (takeBytes 32).run rest with
        | .error e => .error e
        | .ok (hash, suffix) => .ok ({ length, hash }, suffix) := by
  unfold takeRef
  unfold_trie_parser readRef
  simp only [takeNat, takeBytes, StateT.run, bind, StateT.bind]
  cases hn : ((trie_parser readNat) 4) bytes with
  | error e => rfl
  | ok pair =>
    obtain ⟨length, rest⟩ := pair
    cases hb : ((trie_parser readBytes) 32) rest with
    | error e => simp only [Except.bind, hb]
    | ok pair =>
      obtain ⟨hash, suffix⟩ := pair
      simp only [Except.bind, hb]
      rfl

/-- A value reference contains a bounded u32 length and exactly 32 hash bytes. -/
theorem takeRef_parts (length : Nat) (hash suffix : Bytes)
    (hwidth : length < 2 ^ 32) (hhash : hash.length = 32) :
    takeRef.run (littleEndian 4 length ++ hash ++ suffix) = .ok ({ length, hash }, suffix) := by
  rw [takeRef_run, List.append_assoc, takeNat_little4 length (hash ++ suffix) hwidth]
  have hb := takeBytes_append hash suffix
  rw [hhash] at hb
  simp only [hb]

/-- The actual path parser first reads its u32-sized compact byte vector. -/
theorem takePath_run (leaf : Bool) (bytes : Bytes) :
    (takePath leaf).run bytes = match (takeNat 4).run bytes with
      | .error e => .error e
      | .ok (length, rest) => match (takeBytes length).run rest with
        | .error e => .error e
        | .ok (encoded, suffix) => match decodePath leaf encoded with
          | .error e => .error e
          | .ok path => .ok (path, suffix) := by
  unfold takePath
  unfold_trie_parser readPath
  simp only [takeNat, takeBytes, StateT.run, bind, StateT.bind]
  cases hn : ((trie_parser readNat) 4) bytes with
  | error e => rfl
  | ok pair =>
    obtain ⟨length, rest⟩ := pair
    cases hb : ((trie_parser readBytes) length) rest with
    | error e => simp only [Except.bind, hb]
    | ok pair =>
      obtain ⟨encoded, suffix⟩ := pair
      cases hd : decodePath leaf encoded <;> simp only [Except.bind, hb, hd] <;> rfl

/-- Canonical path vectors round-trip with every following field framed. -/
theorem takePath_encoded (leaf : Bool) (path : List Nat) (suffix : Bytes)
    (hpath : ValidPath path) (hroom : (encodePath leaf path).length < 2 ^ 32) :
    (takePath leaf).run (vectorBytes (encodePath leaf path) ++ suffix) = .ok (path, suffix) := by
  rw [takePath_run, vectorBytes_eq, List.append_assoc,
    takeNat_little4 _ _ hroom]
  simp only [takeBytes_append, decodePath_encodePath leaf path hpath]

/-- The actual value-reference encoder always writes a complete hash. -/
theorem takeRef_value (value suffix : Bytes) (hwidth : value.length < 2 ^ 32) :
    takeRef.run (valueRefBytes value ++ suffix) =
      .ok ({ length := value.length, hash := Sha256.hash value }, suffix) := by
  rw [valueRefBytes_eq]
  exact takeRef_parts _ _ _ hwidth (Sha256.hash_length value)

theorem takeNat_zero (suffix : Bytes) :
    (takeNat 1).run (0 :: suffix) = .ok (0, suffix) := by
  simpa using takeNat_append [0] suffix

/-- Parser composition for the leaf variant, including the terminal size and
strict end-of-input check. The hypotheses concern individual field reads. -/
theorem decodeNode_leaf_of_reads (bytes afterTag afterPath afterRef : Bytes)
    (path : List Nat) (value : ValueRef) (usage : Nat)
    (htag : (takeNat 1).run bytes = .ok (0, afterTag))
    (hpath : (takePath true).run afterTag = .ok (path, afterPath))
    (href : takeRef.run afterPath = .ok (value, afterRef))
    (husage : (takeNat 8).run afterRef = .ok (usage, [])) :
    decodeNode bytes = .ok (.leaf path value) := by
  simp only [takeNat, takePath, takeRef, StateT.run] at htag hpath href husage
  simp only [decodeNode, StateT.run, bind, StateT.bind]
  rw [htag]
  try simp only [bind, Except.bind, StateT.bind, pure, StateT.pure, Except.pure]
  rw [hpath]
  simp only []
  rw [href]
  simp only []
  rw [husage]
  rfl

/-- The actual singleton-leaf serialization decodes to its path and value
reference. The three serialization-width requirements are explicit. -/
theorem decodeNode_leaf (path : List Nat) (value : Bytes) (usage : Nat)
    (hpath : ValidPath path) (hpathRoom : (encodePath true path).length < 2 ^ 32)
    (hvalueRoom : value.length < 2 ^ 32) (husageRoom : usage < 2 ^ 64) :
    decodeNode ([0] ++ vectorBytes (encodePath true path) ++ valueRefBytes value ++ littleEndian 8 usage) =
      .ok (.leaf path { length := value.length, hash := Sha256.hash value }) := by
  apply decodeNode_leaf_of_reads _
    (vectorBytes (encodePath true path) ++ (valueRefBytes value ++ littleEndian 8 usage))
    (valueRefBytes value ++ littleEndian 8 usage) (littleEndian 8 usage) path _ usage
  · simpa only [List.cons_append, List.nil_append, List.append_assoc] using
      takeNat_zero (vectorBytes (encodePath true path) ++ (valueRefBytes value ++ littleEndian 8 usage))
  · exact takePath_encoded true path _ hpath hpathRoom
  · exact takeRef_value value _ hvalueRoom
  · simpa using takeNat_little8 usage [] husageRoom

/-- The generic u32 byte-vector parser preserves every following field. -/
theorem takeVector_append (bytes suffix : Bytes) (hroom : bytes.length < 2 ^ 32) :
    ((do let length ← takeNat 4; takeBytes length) : Parser Bytes).run
      (vectorBytes bytes ++ suffix) = .ok (bytes, suffix) := by
  simp only [vectorBytes_eq, List.append_assoc, StateT.run, bind, StateT.bind]
  rw [show (takeNat 4) (littleEndian 4 bytes.length ++ (bytes ++ suffix)) =
    .ok (bytes.length, bytes ++ suffix) from takeNat_little4 _ _ hroom]
  simp only [Except.bind]
  exact takeBytes_append bytes suffix

/-- A raw byte key contributes two valid nibbles per byte. Its compact path
needs exactly one extra byte, and that extra-byte room is stated explicitly. -/
theorem decodeNode_leaf_nibbles (key value : Bytes) (usage : Nat)
    (hkeyRoom : key.length + 1 < 2 ^ 32)
    (hvalueRoom : value.length < 2 ^ 32) (husageRoom : usage < 2 ^ 64) :
    decodeNode ([0] ++ vectorBytes (encodePath true (nibbles key)) ++
      valueRefBytes value ++ littleEndian 8 usage) =
      .ok (.leaf (nibbles key) { length := value.length, hash := Sha256.hash value }) :=
  decodeNode_leaf _ value usage (nibbles_valid key)
    (by rw [encodePath_nibbles_length]; exact hkeyRoom) hvalueRoom husageRoom

end Near.TrieSerialization
