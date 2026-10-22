import Model.Storage

namespace Linkdrop.Storage

@[simp] theorem leBytes_length (w n : Nat) : (leBytes w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [leBytes, ih]

@[simp] theorem vectorBytes_length (bs : Bytes) : (vectorBytes bs).length = 4 + bs.length := by
  simp [vectorBytes]

theorem header_length (n : Nat) : (header n).length = 34 := by
  simp [header, indexPrefix, keysPrefix, valuesPrefix]

theorem entry_record_count (data : Key → Bytes) (s : State) (i k : Nat) :
    (entry data s i k).length = 3 := by rfl

theorem entry_usage (data : Key → Bytes) (s : State) (i k extra : Nat) :
    usage extra (entry data s i k) = 54 + 2 * (data k).length + 3 * extra := by
  simp [usage, entry, recordBytes, indexPrefix, keysPrefix, valuesPrefix]
  omega

theorem ed25519_entry_usage (data : Key → Bytes) (s : State) (i k extra : Nat)
    (h : (data k).length = 33) : usage extra (entry data s i k) = 120 + 3 * extra := by
  rw [entry_usage, h]

theorem secp256k1_entry_usage (data : Key → Bytes) (s : State) (i k extra : Nat)
    (h : (data k).length = 65) : usage extra (entry data s i k) = 184 + 3 * extra := by
  rw [entry_usage, h]

theorem records_count (data : Key → Bytes) (s : State) (order : List Key) (i : Nat) :
    (records data s i order).length = 3 * order.length := by
  induction order generalizing i with
  | nil => simp [records]
  | cons k ks ih => simp [records, ih, entry_record_count]; omega

theorem encode_record_count (data : Key → Bytes) (s : State) (order : List Key)
    (hi : s.initialized = true) :
    (encode data s order).length = 1 + 3 * order.length := by
  simp [encode, hi, records_count, Nat.add_comm]

theorem state_record_usage (n extra : Nat) :
    recordBytes extra (stateKey, header n) = 39 + extra := by
  simp [recordBytes, stateKey, header_length]

theorem usage_append (extra : Nat) (left right : Raw) :
    usage extra (left ++ right) = usage extra left + usage extra right := by
  simp [usage]

theorem records_usage (data : Key → Bytes) (s : State) (order : List Key) (i extra : Nat) :
    usage extra (records data s i order) =
      (order.map fun k => 54 + 2 * (data k).length + 3 * extra).sum := by
  induction order generalizing i with
  | nil => rfl
  | cons k ks ih => simp [records, usage_append, entry_usage, ih]

theorem encode_usage (data : Key → Bytes) (s : State) (order : List Key) (extra : Nat)
    (hi : s.initialized = true) :
    usage extra (encode data s order) = 39 + extra +
      (order.map fun k => 54 + 2 * (data k).length + 3 * extra).sum := by
  simp only [encode, hi, ↓reduceIte]
  change recordBytes extra (stateKey, header order.length) +
    usage extra (records data s 0 order) = _
  rw [state_record_usage, records_usage]

theorem records_usage_bounds (data : Key → Bytes) (s : State) (order : List Key)
    (i extra : Nat) (hv : ∀ k ∈ order, validPublicKey (data k)) :
    (120 + 3 * extra) * order.length ≤ usage extra (records data s i order) ∧
    usage extra (records data s i order) ≤ (184 + 3 * extra) * order.length := by
  induction order generalizing i with
  | nil => simp [records, usage]
  | cons k ks ih =>
    have ih' := ih (i + 1) (by intro j hj; exact hv j (by simp [hj]))
    have hkey := hv k (by simp)
    rcases hkey with ⟨_, hk⟩ | ⟨_, hk⟩
    all_goals
      simp only [records, usage_append, entry_usage, hk, List.length_cons, Nat.mul_add, Nat.mul_one]
      constructor <;> omega

theorem encode_usage_bounds (data : Key → Bytes) (s : State) (order : List Key)
    (extra : Nat) (hi : s.initialized = true)
    (hv : ∀ k ∈ order, validPublicKey (data k)) :
    39 + extra + (120 + 3 * extra) * order.length ≤ usage extra (encode data s order) ∧
    usage extra (encode data s order) ≤ 39 + extra + (184 + 3 * extra) * order.length := by
  have hb := records_usage_bounds data s order 0 extra hv
  simp only [encode, hi, ↓reduceIte]
  change _ ≤ recordBytes extra (stateKey, header order.length) +
    usage extra (records data s 0 order) ∧
    recordBytes extra (stateKey, header order.length) + usage extra (records data s 0 order) ≤ _
  rw [state_record_usage]
  omega

end Linkdrop.Storage
