import NearInterface.TrieConstruction

/-!
# Canonical trie path serialization

These proofs concern the actual compact-path encoder and strict decoder. They
need nibble bounds, without assumptions about hashes or native trie witnesses.
-/
namespace Near.TrieConstruction
open TrieAccounting

-- Name the existing transparent private helper; no packing implementation is
-- duplicated in this proof module.
local macro "actual_path_pack" : term => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "pack"
  pure (Lean.mkIdent name)

/-- A path consists of hexadecimal digits. -/
def ValidPath (path : List Nat) : Prop := ∀ n ∈ path, n < 16

/-- Proof-facing alias of the actual encoder's private byte-packing helper. -/
def packPath (path : List Nat) : Bytes := actual_path_pack path

@[simp] theorem packPath_nil : packPath [] = [] := rfl
@[simp] theorem packPath_singleton (a : Nat) : packPath [a] = [UInt8.ofNat (16 * a)] := rfl
@[simp] theorem packPath_cons (a b : Nat) (rest : List Nat) :
    packPath (a :: b :: rest) = UInt8.ofNat (16 * a + b) :: packPath rest := rfl

/-- Packing uses one byte per digit pair, rounding an odd tail upward. -/
theorem packPath_length : ∀ path : List Nat,
    (packPath path).length = (path.length + 1) / 2
  | [] => rfl
  | [a] => by simp [packPath_singleton]
  | a :: b :: rest => by
    rw [packPath_cons, List.length_cons, packPath_length rest]
    simp only [List.length_cons]
    omega

/-- Every byte yields two valid hexadecimal digits. -/
theorem nibbles_valid (bytes : Bytes) : ValidPath (nibbles bytes) := by
  intro n hn
  obtain ⟨byte, _, hm⟩ := List.mem_flatMap.mp hn
  have hb := UInt8.toNat_lt byte
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> omega

theorem nibbles_length (bytes : Bytes) : (nibbles bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [nibbles, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at *
    omega

/-- Packing a complete sequence of nibble pairs loses no information. -/
theorem nibbles_packPath : ∀ (path : List Nat), ValidPath path → path.length % 2 = 0 →
    nibbles (packPath path) = path
  | [], _, _ => rfl
  | [a], _, heven => by simp at heven
  | a :: b :: rest, hvalid, heven => by
    have ha := hvalid a (by simp)
    have hb := hvalid b (by simp)
    have hn : 16 * a + b < 256 := by omega
    have hnat : (UInt8.ofNat (16 * a + b)).toNat = 16 * a + b := by
      change (16 * a + b) % 256 = 16 * a + b
      exact Nat.mod_eq_of_lt hn
    have hrest : ValidPath rest := fun n hn => hvalid n (by simp [hn])
    have hparity : rest.length % 2 = 0 := by
      simp only [List.length_cons] at heven
      omega
    rw [packPath_cons]
    simp only [nibbles, List.flatMap_cons, List.cons_append, List.nil_append, hnat]
    have hhigh : (16 * a + b) / 16 = a := by omega
    have hlow : (16 * a + b) % 16 = b := by omega
    rw [hhigh, hlow]
    exact congrArg (a :: b :: ·) (nibbles_packPath rest hrest hparity)

theorem encodePath_even (leaf : Bool) (path : List Nat) (heven : path.length % 2 = 0) :
    encodePath leaf path = UInt8.ofNat (if leaf then 32 else 0) :: packPath path := by
  simp only [encodePath, heven, beq_self_eq_true, ↓reduceIte]
  rfl

theorem encodePath_odd (leaf : Bool) (a : Nat) (rest : List Nat)
    (hodd : (a :: rest).length % 2 ≠ 0) :
    encodePath leaf (a :: rest) =
      UInt8.ofNat ((if leaf then 32 else 0) + 16 + a) :: packPath rest := by
  have hp : (a :: rest).length % 2 = 1 := by omega
  have hb : ((a :: rest).length % 2 == 0) = false := by rw [hp]; rfl
  simp only [encodePath, hb, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
  rfl

/-- Compact encoding has one header byte and half as many payload bytes as digits. -/
theorem encodePath_length (leaf : Bool) (path : List Nat) :
    (encodePath leaf path).length = 1 + path.length / 2 := by
  by_cases heven : path.length % 2 = 0
  · rw [encodePath_even leaf path heven, List.length_cons, packPath_length]
    omega
  · cases path with
    | nil => simp at heven
    | cons a rest =>
      rw [encodePath_odd leaf a rest heven, List.length_cons, packPath_length]
      simp only [List.length_cons]
      omega

theorem encodePath_nibbles_length (leaf : Bool) (bytes : Bytes) :
    (encodePath leaf (nibbles bytes)).length = bytes.length + 1 := by
  rw [encodePath_length, nibbles_length]
  omega

/-- The even header encodes only the leaf flag and canonical zero padding. -/
theorem decodePath_even_header (leaf : Bool) (bytes : Bytes) :
    decodePath leaf (UInt8.ofNat (if leaf then 32 else 0) :: bytes) = .ok (nibbles bytes) := by
  cases leaf <;> rfl

/-- The odd header carries the first digit as well as the parity/leaf flags. -/
theorem decodePath_odd_header (leaf : Bool) (a : Nat) (bytes : Bytes) (ha : a < 16) :
    decodePath leaf (UInt8.ofNat ((if leaf then 32 else 0) + 16 + a) :: bytes) =
      .ok (a :: nibbles bytes) := by
  cases leaf with
  | false =>
    have hn : (16 + a) % 256 = 16 + a := Nat.mod_eq_of_lt (by omega)
    have hd : (16 + a) / 16 = 1 := by omega
    have hm : (16 + a) % 16 = a := by omega
    simp [decodePath, hn, hd, hm]
    rfl
  | true =>
    have hn : (48 + a) % 256 = 48 + a := Nat.mod_eq_of_lt (by omega)
    have hd : (48 + a) / 16 = 3 := by omega
    have hm : (48 + a) % 16 = a := by omega
    simp [decodePath, hn, hd, hm]
    rfl

/-- Kernel-checked round trip for the actual compact-path encoder/decoder. -/
theorem decodePath_encodePath (leaf : Bool) (path : List Nat) (hvalid : ValidPath path) :
    decodePath leaf (encodePath leaf path) = .ok path := by
  by_cases heven : path.length % 2 = 0
  · rw [encodePath_even leaf path heven, decodePath_even_header, nibbles_packPath path hvalid heven]
  · cases path with
    | nil => simp at heven
    | cons a rest =>
      have ha := hvalid a (by simp)
      have hrest : ValidPath rest := fun n hn => hvalid n (by simp [hn])
      have hparity : rest.length % 2 = 0 := by
        simp only [List.length_cons] at heven
        omega
      rw [encodePath_odd leaf a rest heven, decodePath_odd_header leaf a _ ha,
        nibbles_packPath rest hrest hparity]

/-- Every byte key has a valid compact path and hence round-trips. -/
theorem decodePath_encodePath_nibbles (leaf : Bool) (bytes : Bytes) :
    decodePath leaf (encodePath leaf (nibbles bytes)) = .ok (nibbles bytes) :=
  decodePath_encodePath leaf _ (nibbles_valid bytes)

/-- Compact encoding is injective on the valid nibble paths for each node kind. -/
theorem encodePath_injective (leaf : Bool) (left right : List Nat)
    (hl : ValidPath left) (hr : ValidPath right)
    (h : encodePath leaf left = encodePath leaf right) : left = right := by
  have hd := congrArg (decodePath leaf) h
  rw [decodePath_encodePath leaf left hl, decodePath_encodePath leaf right hr] at hd
  exact Except.ok.inj hd

end Near.TrieConstruction
