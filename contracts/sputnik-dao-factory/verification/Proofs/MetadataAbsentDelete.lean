import Proofs.MetadataTailRemove

namespace SputnikFactory

/-- The legacy map's absent-key branch does not inspect its vector length or
records. -/
theorem map_remove_absent (header : MapHeader) (raw : Raw) (hash : Hash)
    (habsent : read raw (mapIndexKey header hash) = none) :
    (mapRemove header hash).run raw = .ok (header, raw) := by
  simp [mapRemove, habsent, load, Bind.bind, Pure.pure, Tx.bind, Tx.run]

def metadataHeaderResaved (raw : Raw) (order : List (Hash × Metadata)) : Raw :=
  write raw metadataKey (Borsh.encodeMap (Spec.metadataHeader order))

theorem metadata_header_resave_preserves_layout (raw : Raw)
    (order : List (Hash × Metadata))
    (layout : Spec.MetadataLayout raw order) :
    Spec.MetadataLayout (metadataHeaderResaved raw order) order := by
  constructor
  · exact layout.unique
  · exact read_write_self _ _ _
  · intro hash
    have hne : mapIndexKey initialMap hash ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, hash.property] at hlen
    unfold metadataHeaderResaved
    rw [read_write_other _ _ _ _ hne]
    exact layout.index hash
  · intro index hindex
    have hne : vectorKey initialMap.keys index ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlen
    unfold metadataHeaderResaved
    rw [read_write_other _ _ _ _ hne]
    exact layout.key index hindex
  · intro index hindex
    have hne : vectorKey initialMap.values index ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlen
    unfold metadataHeaderResaved
    rw [read_write_other _ _ _ _ hne]
    exact layout.value index hindex

theorem delete_absent_metadata_entry (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash)
    (layout : Spec.MetadataLayout raw order)
    (horderLength : order.length < 256 ^ 8)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.deleteMetadata hash) =
      .ok ⟨metadataHeaderResaved raw order, [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader order)) =
      some (Spec.metadataHeader order) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderLength
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderLength
    · simp [Spec.metadataHeader, initialMap]
  have habsent' : read raw (mapIndexKey (Spec.metadataHeader order) hash) =
      none := by
    simpa [Spec.metadataHeader, mapIndexKey] using habsent
  have hremove := map_remove_absent (Spec.metadataHeader order) raw hash habsent'
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, loadMap, layout.header, hmap, hremove, metadataHeaderResaved,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem delete_absent_metadata_preserves_layout (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash)
    (layout : Spec.MetadataLayout raw order)
    (horderLength : order.length < 256 ^ 8)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata hash) = .ok out) :
    Spec.MetadataLayout out.raw order := by
  rw [delete_absent_metadata_entry cfg raw env setHeader order hash layout
    horderLength habsent hstate hsetIndex hsetLength hsetPrefix howner] at hstep
  cases hstep
  exact metadata_header_resave_preserves_layout raw order layout

theorem metadata_header_resave_preserves_state (raw : Raw)
    (order : List (Hash × Metadata)) :
    read (metadataHeaderResaved raw order) stateKey = read raw stateKey := by
  unfold metadataHeaderResaved
  exact read_write_other raw metadataKey stateKey _ (by decide)

theorem delete_absent_metadata_then_get (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash)
    (layout : Spec.MetadataLayout raw order)
    (horderLength : order.length < 256 ^ 8)
    (hbounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata hash) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata order⟩ := by
  rw [delete_absent_metadata_entry cfg raw env setHeader order hash layout
    horderLength habsent hstate hsetIndex hsetLength hsetPrefix howner] at hstep
  cases hstep
  have hstate' : read (metadataHeaderResaved raw order) stateKey =
      some (Borsh.encodeSet setHeader) := by
    rw [metadata_header_resave_preserves_state]
    exact hstate
  exact metadata_getter_matches_layout cfg _ env setHeader order hstate'
    hsetIndex hsetLength hsetPrefix
    (metadata_header_resave_preserves_layout raw order layout)
    horderLength hbounded

end SputnikFactory
