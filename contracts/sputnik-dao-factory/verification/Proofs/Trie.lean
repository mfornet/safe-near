import Model.Storage

namespace SputnikFactory

theorem read_write_self (raw : Raw) (key value : Bytes) :
    read (write raw key value) key = some value := by
  simp [read, write]

theorem read_remove_self (raw : Raw) (key : Bytes) : read (remove raw key) key = none := by
  unfold read
  rw [List.lookup_eq_none_iff]
  intro pair hp
  have hf := (List.mem_filter.mp hp).2
  simpa [ne_comm] using hf

theorem read_remove_other (raw : Raw) (key query : Bytes) (h : query ≠ key) :
    read (remove raw key) query = read raw query := by
  induction raw with
  | nil => rfl
  | cons pair tail ih =>
    rcases pair with ⟨p, v⟩
    simp only [read, remove] at ih
    by_cases he : p = key
    · subst p
      simpa [read, remove, List.lookup_cons, beq_eq_false_iff_ne.mpr h] using ih
    · cases hb : query == p <;> simp [read, remove, List.lookup_cons, he, hb, ih]

theorem read_write_other (raw : Raw) (key query value : Bytes) (h : query ≠ key) :
    read (write raw key value) query = read raw query := by
  simp only [read, write, List.lookup_cons]
  rw [beq_eq_false_iff_ne.mpr h]
  exact read_remove_other raw key query h

theorem remove_wf (raw : Raw) (key : Bytes) (h : raw.WF) : (remove raw key).WF := by
  exact (List.filter_sublist.map Prod.fst).nodup h

theorem write_wf (raw : Raw) (key value : Bytes) (h : raw.WF) : (write raw key value).WF := by
  change (key :: (remove raw key).map Prod.fst).Nodup
  rw [List.nodup_cons]
  constructor
  · intro hk
    obtain ⟨pair, hp, he⟩ := List.mem_map.mp hk
    have hf := (List.mem_filter.mp hp).2
    simp [he] at hf
  · exact remove_wf raw key h

/-- Default-hash values never alias the OWNER or STATE headers: those are short
fixed keys. This lemma is independent of whether the supplied hash names code. -/
theorem set_default_preserves_owner (raw : Raw) (hash : Hash) (out : Raw)
    (h : setDefaultAfterAuthorization raw hash = .ok out) :
    read out ownerKey = read raw ownerKey := by
  unfold setDefaultAfterAuthorization at h
  split at h <;> simp_all
  subst out
  exact read_write_other raw defaultKey ownerKey hash.val (by decide)

end SputnikFactory
