import Proofs.Storage

namespace Linkdrop.Storage

/-- Mathematical fixed-width decoding, with no compiler-trusted reduction. -/
def fromLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * fromLE bs

theorem fromLE_leBytes (width n : Nat) (h : n < 256 ^ width) :
    fromLE (leBytes width n) = n := by
  induction width generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn, fromLE, leBytes]
  | succ width ih =>
    have hdiv : n / 256 < 256 ^ width := by
      rw [Nat.pow_succ] at h
      omega
    simp only [leBytes, fromLE, UInt8.toNat_ofNat', ih _ hdiv]
    have hm : n % 256 < 256 := Nat.mod_lt _ (by decide)
    change n % 256 % 256 + 256 * (n / 256) = n
    rw [Nat.mod_eq_of_lt hm]
    omega

theorem leBytes_injective {width n m : Nat} (hn : n < 256 ^ width) (hm : m < 256 ^ width)
    (h : leBytes width n = leBytes width m) : n = m := by
  have he := congrArg fromLE h
  simpa [fromLE_leBytes _ _ hn, fromLE_leBytes _ _ hm] using he

theorem vectorBytes_injective {a b : Bytes} (h : vectorBytes a = vectorBytes b) : a = b := by
  have he := congrArg (List.drop 4) h
  simpa [vectorBytes, List.drop_append, List.drop_eq_nil_of_le] using he

theorem records_mem_iff (data : Key → Bytes) (s : State) (order : List Key)
    (start : Nat) (pair : Bytes × Bytes) :
    pair ∈ records data s start order ↔
      ∃ offset key, order[offset]? = some key ∧ pair ∈ entry data s (start + offset) key := by
  induction order generalizing start with
  | nil => simp [records]
  | cons head tail ih =>
    simp only [records, List.mem_append]
    constructor
    · rintro (h | h)
      · exact ⟨0, head, by simp, by simpa using h⟩
      · obtain ⟨offset, key, hk, hp⟩ := (ih (start + 1)).mp h
        exact ⟨offset + 1, key, by simpa using hk, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩
    · rintro ⟨offset, key, hk, hp⟩
      cases offset with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst key
        exact Or.inl (by simpa using hp)
      | succ offset =>
        right
        apply (ih (start + 1)).mpr
        exact ⟨offset, key, by simpa using hk, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩

/-- The key-index record can be distinguished from key/value-vector records by
its prefix. The payload is an SDK Borsh PublicKey, not an arbitrary raw key. -/
theorem index_record_entry_iff (data : Key → Bytes) (s : State) (i key query : Nat) (v : Bytes) :
    (indexPrefix ++ vectorBytes (data query), v) ∈ entry data s i key ↔
      vectorBytes (data query) = vectorBytes (data key) ∧ v = leBytes 8 i := by
  simp [entry, indexPrefix, keysPrefix, valuesPrefix]

theorem value_record_entry_iff (data : Key → Bytes) (s : State) (i key : Nat) (query v : Bytes) :
    (valuesPrefix ++ query, v) ∈ entry data s i key ↔
      query = leBytes 8 i ∧ v = leBytes 16 ((s.accounts key).getD 0) := by
  simp [entry, indexPrefix, keysPrefix, valuesPrefix]

theorem stateKey_not_in_records (data : Key → Bytes) (s : State) (order : List Key) (i : Nat)
    (v : Bytes) : (stateKey, v) ∉ records data s i order := by
  rw [records_mem_iff]
  rintro ⟨offset, key, _, h⟩
  simp [entry, stateKey, indexPrefix, keysPrefix, valuesPrefix] at h

theorem state_record_encode_iff (data : Key → Bytes) (s : State) (order : List Key) (v : Bytes) :
    (stateKey, v) ∈ encode data s order ↔ s.initialized = true ∧ v = header order.length := by
  cases hi : s.initialized <;>
    simp [encode, hi, stateKey_not_in_records]

theorem index_record_encode_iff (data : Key → Bytes) (s : State) (order : List Key)
    (query : Key) (v : Bytes) (hi : s.initialized = true) :
    (indexPrefix ++ vectorBytes (data query), v) ∈ encode data s order ↔
      ∃ offset key, order[offset]? = some key ∧
        vectorBytes (data query) = vectorBytes (data key) ∧ v = leBytes 8 offset := by
  simp only [encode, hi, ↓reduceIte, List.mem_cons]
  have hne : indexPrefix ++ vectorBytes (data query) ≠ stateKey := by
    simp [indexPrefix, stateKey]
  simp only [Prod.mk.injEq, hne, false_and, false_or]
  rw [records_mem_iff]
  simp only [index_record_entry_iff, Nat.zero_add]

theorem value_record_encode_iff (data : Key → Bytes) (s : State) (order : List Key)
    (query v : Bytes) (hi : s.initialized = true) :
    (valuesPrefix ++ query, v) ∈ encode data s order ↔
      ∃ offset key, order[offset]? = some key ∧
        query = leBytes 8 offset ∧ v = leBytes 16 ((s.accounts key).getD 0) := by
  simp only [encode, hi, ↓reduceIte, List.mem_cons]
  have hne : valuesPrefix ++ query ≠ stateKey := by simp [valuesPrefix, stateKey]
  simp only [Prod.mk.injEq, hne, false_and, false_or]
  rw [records_mem_iff]
  simp only [value_record_entry_iff, Nat.zero_add]

theorem initialized_of_some {s : State} {key amount : Nat} (hwf : s.WF)
    (hk : s.accounts key = some amount) : s.initialized = true := by
  cases hi : s.initialized with
  | false => have he := hwf.2 hi key; simp_all
  | true => rfl

theorem amount_lt_encoding_bound {n : Nat} (h : n ≤ maxAmount) : n < 256 ^ 16 := by
  change n ≤ 340282366920938463463374607431768211455 at h
  change n < 340282366920938463463374607431768211456
  omega

/-- Membership in the three SDK records forces an identical logical balance in
any other valid representation of exactly the same raw storage. -/
theorem encoded_some_unique (data : Key → Bytes) (s t : State) (left right : List Key)
    (hs : LayoutValid data s left) (ht : LayoutValid data t right)
    (hp : (encode data s left).Perm (encode data t right))
    (key amount : Nat) (hk : s.accounts key = some amount) :
    t.accounts key = some amount := by
  obtain ⟨hswf, _, hslen, hscov, _, _⟩ := hs
  obtain ⟨htwf, _, htlen, htcov, _, hinj⟩ := ht
  have hsi := initialized_of_some hswf hk
  have headerMem : (stateKey, header left.length) ∈ encode data s left :=
    (state_record_encode_iff data s left _).mpr ⟨hsi, rfl⟩
  have hti := ((state_record_encode_iff data t right _).mp (hp.mem_iff.mp headerMem)).1
  have hkmem : key ∈ left := (hscov key).mpr (by simp [hk])
  obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp hkmem
  have hib : i < 256 ^ 8 := by
    have hb := (List.getElem?_eq_some_iff.mp hget).choose
    exact Nat.lt_trans hb hslen
  have hindex : (indexPrefix ++ vectorBytes (data key), leBytes 8 i) ∈ encode data s left :=
    (index_record_encode_iff data s left key _ hsi).mpr ⟨i, key, hget, rfl, rfl⟩
  obtain ⟨j, other, hget', hdata, heqij⟩ :=
    (index_record_encode_iff data t right key _ hti).mp (hp.mem_iff.mp hindex)
  have hkey : key = other := hinj key other (vectorBytes_injective hdata)
  subst other
  have hjb : j < 256 ^ 8 := Nat.lt_trans (List.getElem?_eq_some_iff.mp hget').choose htlen
  have hij : i = j := leBytes_injective hib hjb heqij
  subst j
  have hvalue : (valuesPrefix ++ leBytes 8 i, leBytes 16 amount) ∈ encode data s left :=
    (value_record_encode_iff data s left _ _ hsi).mpr ⟨i, key, hget, rfl, by simp [hk]⟩
  obtain ⟨j, other, hget'', heqij', hvalue'⟩ :=
    (value_record_encode_iff data t right _ _ hti).mp (hp.mem_iff.mp hvalue)
  have hjb' : j < 256 ^ 8 := Nat.lt_trans (List.getElem?_eq_some_iff.mp hget'').choose htlen
  have hij' : i = j := leBytes_injective hib hjb' heqij'
  subst j
  have hkey' : key = other := by rw [hget'] at hget''; simpa using hget''
  subst other
  have hkmem' : key ∈ right := List.mem_iff_getElem?.mpr ⟨i, hget'⟩
  have hsome := (htcov key).mp hkmem'
  cases hv : t.accounts key with
  | none => simp [hv] at hsome
  | some n =>
    have hn := htwf.1 key n hv
    simp only [hv, Option.getD_some] at hvalue'
    have he : amount = n := leBytes_injective
      (amount_lt_encoding_bound (hswf.1 key amount hk)) (amount_lt_encoding_bound hn) hvalue'
    simp [he]

theorem encoded_state_unique (data : Key → Bytes) (s t : State) (left right : List Key)
    (hs : LayoutValid data s left) (ht : LayoutValid data t right)
    (hp : (encode data s left).Perm (encode data t right)) : s = t := by
  have hinit : s.initialized = t.initialized := by
    have hlength := hp.length_eq
    cases hi : s.initialized <;> cases hj : t.initialized <;>
      simp_all [encode]
  have haccounts : s.accounts = t.accounts := by
    funext key
    cases hk : s.accounts key with
    | none =>
      cases hk' : t.accounts key with
      | none => rfl
      | some n =>
        have he := encoded_some_unique data t s right left ht hs hp.symm key n hk'
        simp [hk] at he
    | some n => exact (encoded_some_unique data s t left right hs ht hp key n hk).symm
  cases s
  cases t
  cases hinit
  cases haccounts
  rfl

theorem represents_unique (data : Key → Bytes) (raw : Raw) (s t : State)
    (hs : Represents data raw s) (ht : Represents data raw t) : s = t := by
  obtain ⟨left, hsl, hsp⟩ := hs
  obtain ⟨right, htl, htp⟩ := ht
  exact encoded_state_unique data s t left right hsl htl (hsp.symm.trans htp)

/-- Every valid physical encoding projects to its original logical state, even
though different vector orders can encode the same logical balances differently. -/
theorem project_encode (data : Key → Bytes) (s : State) (order : List Key)
    (hs : LayoutValid data s order) : project data (encode data s order) = some s := by
  have hr : Represents data (encode data s order) s := ⟨order, hs, .refl _⟩
  unfold project
  split
  · rename_i h
    exact congrArg some (represents_unique data _ _ s (Classical.choose_spec h) hr)
  · rename_i h
    exact False.elim (h ⟨s, hr⟩)

theorem project_of_represents (data : Key → Bytes) (raw : Raw) (s : State)
    (hs : Represents data raw s) : project data raw = some s := by
  unfold project
  split
  · rename_i h
    exact congrArg some (represents_unique data raw _ s (Classical.choose_spec h) hs)
  · rename_i h
    exact False.elim (h ⟨s, hs⟩)

end Linkdrop.Storage
