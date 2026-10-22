import Proofs.MetadataSwapRemove

namespace SputnikFactory

/-- Removing the final vector slot uses pop directly; it never rewrites slot
zero. -/
theorem vector_swap_remove_two_last (header : VectorHeader) (raw : Raw)
    (last : Bytes) (hlen : header.length = 2)
    (hlast : read raw (vectorKey header 1) = some last) :
    (vectorSwapRemove header 1).run raw =
      .ok ((last, { header with length := 1 }),
        remove raw (vectorKey header 1)) := by
  have hpop := vector_pop_two header raw last hlen hlast
  simp [vectorSwapRemove, hlen, hpop, require, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

def twoMetadataTailRemovedRaw (raw : Raw) (second : Hash) : Raw :=
  remove
    (remove
      (remove raw (mapIndexKey initialMap second))
      (vectorKey initialMap.keys 1))
    (vectorKey initialMap.values 1)

theorem two_metadata_remove_last (raw : Raw)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)])
    (hbounded : Spec.MetadataBounded secondValue) :
    (mapRemove (Spec.metadataHeader
      [(first, firstValue), (second, secondValue)]) second).run raw =
      .ok (Spec.metadataHeader [(first, firstValue)],
        twoMetadataTailRemovedRaw raw second) := by
  have hdistinct : first ≠ second := by
    simpa using layout.unique
  have hindex : read raw (mapIndexKey initialMap second) =
      some (leBytes 8 1) := by
    have h := layout.index second
    have hneq : first.val ≠ second.val := by
      intro he
      exact hdistinct (Subtype.ext he)
    simpa [Spec.findHash, hneq] using h
  have hkey1 : read raw (vectorKey initialMap.keys 1) = some second.val := by
    simpa using layout.key 1 (by simp)
  have hvalue1 : read raw (vectorKey initialMap.values 1) =
      some (Borsh.encodeMetadata secondValue) := by
    simpa using layout.value 1 (by simp)
  have hlastGet : (vectorGet (Spec.metadataHeader
      [(first, firstValue), (second, secondValue)]).keys 1).run raw =
      .ok (some second.val, raw) := by
    apply vector_get_present
    · simp [Spec.metadataHeader]
    · simpa [Spec.metadataHeader, vectorKey] using hkey1
  have hkeyAfter : read (remove raw (mapIndexKey initialMap second))
      (vectorKey initialMap.keys 1) = some second.val := by
    rw [read_remove_other _ _ _
      (vector_key_not_metadata_index initialMap.keys 1 second (by decide))]
    exact hkey1
  have hvalueAfter : read
      (remove (remove raw (mapIndexKey initialMap second))
        (vectorKey initialMap.keys 1))
      (vectorKey initialMap.values 1) =
      some (Borsh.encodeMetadata secondValue) := by
    rw [read_remove_other _ _ _ (by decide)]
    rw [read_remove_other _ _ _
      (vector_key_not_metadata_index initialMap.values 1 second (by decide))]
    exact hvalue1
  have hkeys := vector_swap_remove_two_last
    (Spec.metadataHeader [(first, firstValue), (second, secondValue)]).keys
    (remove raw (mapIndexKey initialMap second)) second.val
    (by simp [Spec.metadataHeader])
    (by simpa [Spec.metadataHeader, vectorKey] using hkeyAfter)
  have hvalues := vector_swap_remove_two_last
    (Spec.metadataHeader [(first, firstValue), (second, secondValue)]).values
    (remove (remove raw (mapIndexKey initialMap second))
      (vectorKey initialMap.keys 1)) (Borsh.encodeMetadata secondValue)
    (by simp [Spec.metadataHeader])
    (by simpa [Spec.metadataHeader, vectorKey] using hvalueAfter)
  have hdecode : Borsh.exact (Borsh.natural 8) (leBytes 8 1) = some 1 := by decide
  have hmetadata := exact_metadata_encode_bounded secondValue hbounded.1 hbounded.2
  simp [Spec.metadataHeader, initialMap, mapIndexKey, vectorKey] at hindex hlastGet hkeys hvalues
  simp [mapRemove, Spec.metadataHeader, initialMap, mapIndexKey, vectorKey,
    hindex, hlastGet, hdecode, hkeys, hvalues, hmetadata,
    twoMetadataTailRemovedRaw, mapLength, load, erase, require, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

def twoMetadataTailDeletedRaw (raw : Raw) (first second : Hash)
    (firstValue : Metadata) : Raw :=
  write (twoMetadataTailRemovedRaw raw second) metadataKey
    (Borsh.encodeMap (Spec.metadataHeader [(first, firstValue)]))

theorem two_metadata_delete_last_entry (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)])
    (hbounded : Spec.MetadataBounded secondValue)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.deleteMetadata second) =
      .ok ⟨twoMetadataTailDeletedRaw raw first second firstValue, [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader
        [(first, firstValue), (second, secondValue)])) =
      some (Spec.metadataHeader
        [(first, firstValue), (second, secondValue)]) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
  have hremove := two_metadata_remove_last raw first second firstValue
    secondValue layout hbounded
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, loadMap, layout.header, hmap, hremove, twoMetadataTailDeletedRaw,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem two_metadata_delete_last_preserves_layout (raw : Raw)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)]) :
    Spec.MetadataLayout (twoMetadataTailDeletedRaw raw first second firstValue)
      [(first, firstValue)] := by
  have hdistinct : first ≠ second := by
    simpa using layout.unique
  constructor
  · simp
  · exact read_write_self _ _ _
  · intro query
    have hheader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
    have hvalue : mapIndexKey initialMap query ≠ vectorKey initialMap.values 1 := by
      exact (vector_key_not_metadata_index initialMap.values 1 query (by decide)).symm
    have hkey : mapIndexKey initialMap query ≠ vectorKey initialMap.keys 1 := by
      exact (vector_key_not_metadata_index initialMap.keys 1 query (by decide)).symm
    unfold twoMetadataTailDeletedRaw twoMetadataTailRemovedRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_remove_other _ _ _ hvalue]
    rw [read_remove_other _ _ _ hkey]
    by_cases hq : query = second
    · subst query
      have hneqval : first.val ≠ second.val := by
        intro he
        exact hdistinct (Subtype.ext he)
      simp [read_remove_self, Spec.findHash, hneqval]
    · have hnotIndex : mapIndexKey initialMap query ≠
          mapIndexKey initialMap second := by
        intro he
        exact hq (canonical_map_index_injective query second he)
      rw [read_remove_other _ _ _ hnotIndex]
      have hnotVal : second.val ≠ query.val := by
        intro he
        exact hq (Subtype.ext he.symm)
      simpa [Spec.findHash, hnotVal] using layout.index query
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hheader : vectorKey initialMap.keys 0 ≠ metadataKey := by decide
    have hvalue : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.values 1 := by decide
    have hkey : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.keys 1 := by
      simp [vectorKey, initialMap, leBytes]
    have hindexKey : vectorKey initialMap.keys 0 ≠ mapIndexKey initialMap second :=
      vector_key_not_metadata_index initialMap.keys 0 second (by decide)
    unfold twoMetadataTailDeletedRaw twoMetadataTailRemovedRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_remove_other _ _ _ hvalue]
    rw [read_remove_other _ _ _ hkey]
    rw [read_remove_other _ _ _ hindexKey]
    simpa using layout.key 0 (by simp)
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hheader : vectorKey initialMap.values 0 ≠ metadataKey := by decide
    have hvalue : vectorKey initialMap.values 0 ≠ vectorKey initialMap.values 1 := by
      simp [vectorKey, initialMap, leBytes]
    have hkey : vectorKey initialMap.values 0 ≠ vectorKey initialMap.keys 1 := by decide
    have hindexKey : vectorKey initialMap.values 0 ≠ mapIndexKey initialMap second :=
      vector_key_not_metadata_index initialMap.values 0 second (by decide)
    unfold twoMetadataTailDeletedRaw twoMetadataTailRemovedRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_remove_other _ _ _ hvalue]
    rw [read_remove_other _ _ _ hkey]
    rw [read_remove_other _ _ _ hindexKey]
    simpa using layout.value 0 (by simp)

theorem two_metadata_delete_last_preserves_state (raw : Raw)
    (first second : Hash) (firstValue : Metadata) :
    read (twoMetadataTailDeletedRaw raw first second firstValue) stateKey =
      read raw stateKey := by
  have hindex : stateKey ≠ mapIndexKey initialMap second := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, second.property] at hlen
  unfold twoMetadataTailDeletedRaw twoMetadataTailRemovedRaw
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ metadataKey)]
  rw [read_remove_other _ _ _ (by decide : stateKey ≠ vectorKey initialMap.values 1)]
  rw [read_remove_other _ _ _ (by decide : stateKey ≠ vectorKey initialMap.keys 1)]
  rw [read_remove_other _ _ _ hindex]

theorem two_metadata_delete_last_then_get (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)])
    (hboundedFirst : Spec.MetadataBounded firstValue)
    (hboundedSecond : Spec.MetadataBounded secondValue)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata second) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata [(first, firstValue)]⟩ := by
  rw [two_metadata_delete_last_entry cfg raw env setHeader first second firstValue
    secondValue layout hboundedSecond hstate hsetIndex hsetLength hsetPrefix howner]
    at hstep
  cases hstep
  have hstate' : read (twoMetadataTailDeletedRaw raw first second firstValue)
      stateKey = some (Borsh.encodeSet setHeader) := by
    rw [two_metadata_delete_last_preserves_state]
    exact hstate
  apply metadata_getter_matches_layout cfg _ env setHeader
    [(first, firstValue)] hstate' hsetIndex hsetLength hsetPrefix
  · exact two_metadata_delete_last_preserves_layout raw first second firstValue
      secondValue layout
  · simp
  · intro entry hentry
    simp at hentry
    subst entry
    exact hboundedFirst

end SputnikFactory
