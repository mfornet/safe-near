import Proofs.Storage

namespace SputnikFactory

theorem vector_get_present (header : VectorHeader) (raw : Raw)
    (index : Nat) (value : Bytes)
    (hindex : index < header.length)
    (hread : read raw (vectorKey header index) = some value) :
    (vectorGet header index).run raw = .ok (some value, raw) := by
  have hnot : ¬header.length ≤ index := by omega
  simp [vectorGet, hnot, hread, load, expect,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

theorem metadata_cons_reads (raw : Raw) (order : List (Hash × Metadata))
    (layout : Spec.MetadataLayout raw order)
    (bounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (index : Nat) (hash : Hash) (value : Metadata)
    (indexes : List Nat) (entries : List (Hash × Metadata))
    (hentry : order[index]? = some (hash, value))
    (hrest : (metadataAt (Spec.metadataHeader order) indexes).run raw =
      .ok (entries, raw)) :
    (metadataAt (Spec.metadataHeader order) (index :: indexes)).run raw =
      .ok ((hash, value) :: entries, raw) := by
  have hindex : index < order.length := (List.getElem?_eq_some_iff.mp hentry).1
  have hkey := layout.key index hindex
  have hvalue := layout.value index hindex
  simp [hentry] at hkey hvalue
  have hbound := bounded (hash, value) (List.mem_of_getElem? hentry)
  have hhash : Borsh.hash hash.val = some hash := by
    simp [Borsh.hash, hash.property]
  have hmetadata := exact_metadata_encode_bounded value hbound.1 hbound.2
  have hk : (vectorGet (Spec.metadataHeader order).keys index).run raw =
      .ok (some hash.val, raw) := by
    apply vector_get_present
    · simpa [Spec.metadataHeader] using hindex
    · simpa [Spec.metadataHeader, vectorKey] using hkey
  have hv : (vectorGet (Spec.metadataHeader order).values index).run raw =
      .ok (some (Borsh.encodeMetadata value), raw) := by
    apply vector_get_present
    · simpa [Spec.metadataHeader] using hindex
    · simpa [Spec.metadataHeader, vectorKey] using hvalue
  simp [metadataAt, hk, hv, hhash, hmetadata, hrest, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem metadata_entry_reads (raw : Raw) (order : List (Hash × Metadata))
    (layout : Spec.MetadataLayout raw order)
    (bounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (index : Nat) (hash : Hash) (value : Metadata)
    (hentry : order[index]? = some (hash, value)) :
    (metadataAt (Spec.metadataHeader order) [index]).run raw =
      .ok ([(hash, value)], raw) := by
  exact metadata_cons_reads raw order layout bounded index hash value [] [] hentry rfl

/-- The raw key/value vectors project to the selected logical entries in the
same order, for every valid index list. -/
theorem metadata_indices_project (raw : Raw) (order : List (Hash × Metadata))
    (layout : Spec.MetadataLayout raw order)
    (bounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (indexes : List Nat) (entries : List (Hash × Metadata))
    (hselect : Spec.selectEntries order indexes = some entries) :
    (metadataAt (Spec.metadataHeader order) indexes).run raw =
      .ok (entries, raw) := by
  induction indexes generalizing entries with
  | nil =>
    simp [Spec.selectEntries] at hselect
    subst entries
    rfl
  | cons index indexes ih =>
    cases hentry : order[index]? with
    | none =>
      simp [Spec.selectEntries, hentry] at hselect
    | some entry =>
      rcases entry with ⟨hash, value⟩
      cases htail : Spec.selectEntries order indexes with
      | none =>
        simp [Spec.selectEntries, hentry, htail] at hselect
      | some rest =>
        simp [Spec.selectEntries, hentry, htail] at hselect
        subst entries
        exact metadata_cons_reads raw order layout bounded index hash value
          indexes rest hentry (ih rest htail)

theorem select_entries_cons_succ (head : Hash × Metadata)
    (tail : List (Hash × Metadata)) (indexes : List Nat) :
    Spec.selectEntries (head :: tail) (indexes.map Nat.succ) =
      Spec.selectEntries tail indexes := by
  induction indexes with
  | nil => rfl
  | cons index indexes ih =>
    simp [Spec.selectEntries, ih]

theorem select_entries_complete (order : List (Hash × Metadata)) :
    Spec.selectEntries order (List.range order.length) = some order := by
  induction order with
  | nil => rfl
  | cons head tail ih =>
    change Spec.selectEntries (head :: tail) (List.range (tail.length + 1)) =
      some (head :: tail)
    rw [List.range_succ_eq_map]
    simp [Spec.selectEntries, select_entries_cons_succ, ih]

theorem metadata_vector_projects_order (raw : Raw)
    (order : List (Hash × Metadata))
    (layout : Spec.MetadataLayout raw order)
    (bounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2) :
    (metadataAt (Spec.metadataHeader order) (List.range order.length)).run raw =
      .ok (order, raw) := by
  exact metadata_indices_project raw order layout bounded _ _
    (select_entries_complete order)

/-- The exported getter returns the exact physical vector order of a coherent
metadata map; no sorting or independent logical map is substituted. -/
theorem metadata_getter_matches_layout (cfg : Config) (raw : Raw) (env : Env)
    (setHeader : SetHeader) (order : List (Hash × Metadata))
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (layout : Spec.MetadataLayout raw order)
    (horderLength : order.length < 256 ^ 8)
    (bounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2) :
    step cfg raw env .getMetadata = .ok ⟨raw, [], .metadata order⟩ := by
  have hs := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hm : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader order)) =
      some (Spec.metadataHeader order) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderLength
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderLength
    · simp [Spec.metadataHeader, initialMap]
  have hproject := metadata_vector_projects_order raw order layout bounded
  have hmatching : (Spec.metadataHeader order).keys.length =
      (Spec.metadataHeader order).values.length := rfl
  have hvalueLength : (Spec.metadataHeader order).values.length = order.length := rfl
  simp [step, entry, loadFactory, loadMap, hstate, layout.header, hs, hm,
    body, mapLength, hmatching, hvalueLength, done, Call.private, Call.rejectDeposit,
    Call.isNew, Call.ownerOnly, Call.saveHeader, require, expect, load,
    Bind.bind, Pure.pure, Tx.run_bind, hproject, Tx.bind, Tx.run, Except.bind]

end SputnikFactory
