import Proofs.MetadataSecondInsert

namespace SputnikFactory

theorem vector_pop_singleton (header : VectorHeader) (raw : Raw)
    (previous : Bytes) (hlen : header.length = 1)
    (hread : read raw (vectorKey header 0) = some previous) :
    (vectorPop header).run raw =
      .ok (some (previous, { header with length := 0 }),
        remove raw (vectorKey header 0)) := by
  simp [vectorPop, hlen, hread, load, erase, expect,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

theorem vector_swap_remove_singleton (header : VectorHeader) (raw : Raw)
    (previous : Bytes) (hlen : header.length = 1)
    (hread : read raw (vectorKey header 0) = some previous) :
    (vectorSwapRemove header 0).run raw =
      .ok ((previous, { header with length := 0 }),
        remove raw (vectorKey header 0)) := by
  have hpop := vector_pop_singleton header raw previous hlen hread
  simp [vectorSwapRemove, hlen, hpop, require, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

def singletonMetadataRemovedRaw (raw : Raw) (hash : Hash) : Raw :=
  remove
    (remove
      (remove raw (mapIndexKey initialMap hash))
      (vectorKey initialMap.keys 0))
    (vectorKey initialMap.values 0)

theorem singleton_metadata_remove (raw : Raw) (hash : Hash)
    (value : Metadata)
    (layout : Spec.MetadataLayout raw [(hash, value)])
    (hbounded : Spec.MetadataBounded value) :
    (mapRemove (Spec.metadataHeader [(hash, value)]) hash).run raw =
      .ok (Spec.metadataHeader [], singletonMetadataRemovedRaw raw hash) := by
  have hindex : read raw
      (mapIndexKey (Spec.metadataHeader [(hash, value)]) hash) =
      some (leBytes 8 0) := by
    simpa [Spec.metadataHeader, mapIndexKey, Spec.findHash] using layout.index hash
  have hkey : read raw (vectorKey initialMap.keys 0) = some hash.val := by
    simpa using layout.key 0 (by simp)
  have hvalue : read raw (vectorKey initialMap.values 0) =
      some (Borsh.encodeMetadata value) := by
    simpa using layout.value 0 (by simp)
  have hkeyAfter : read (remove raw (mapIndexKey initialMap hash))
      (vectorKey initialMap.keys 0) = some hash.val := by
    have hne : vectorKey initialMap.keys 0 ≠ mapIndexKey initialMap hash := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, mapIndexKey, initialMap, hash.property] at hlen
    rw [read_remove_other _ _ _ hne]
    exact hkey
  have hvalueAfter : read
      (remove (remove raw (mapIndexKey initialMap hash))
        (vectorKey initialMap.keys 0))
      (vectorKey initialMap.values 0) =
      some (Borsh.encodeMetadata value) := by
    have hneIndex : vectorKey initialMap.values 0 ≠ mapIndexKey initialMap hash := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, mapIndexKey, initialMap, hash.property] at hlen
    have hneKey : vectorKey initialMap.values 0 ≠ vectorKey initialMap.keys 0 := by
      decide
    rw [read_remove_other _ _ _ hneKey]
    rw [read_remove_other _ _ _ hneIndex]
    exact hvalue
  have hdecode : Borsh.exact (Borsh.natural 8) (leBytes 8 0) = some 0 := by decide
  have hmetadata := exact_metadata_encode_bounded value hbounded.1 hbounded.2
  have hkeys := vector_swap_remove_singleton
    (Spec.metadataHeader [(hash, value)]).keys
    (remove raw (mapIndexKey initialMap hash)) hash.val
    (by simp [Spec.metadataHeader]) (by
      simpa [Spec.metadataHeader, vectorKey] using hkeyAfter)
  have hvalues := vector_swap_remove_singleton
    (Spec.metadataHeader [(hash, value)]).values
    (remove (remove raw (mapIndexKey initialMap hash))
      (vectorKey initialMap.keys 0)) (Borsh.encodeMetadata value)
    (by simp [Spec.metadataHeader]) (by
      simpa [Spec.metadataHeader, vectorKey] using hvalueAfter)
  simp [Spec.metadataHeader, initialMap, mapIndexKey, vectorKey] at hindex hkeys hvalues
  have hrun :
      (mapRemove (Spec.metadataHeader [(hash, value)]) hash).run raw =
        .ok ({ Spec.metadataHeader [(hash, value)] with
          keys := { (Spec.metadataHeader [(hash, value)]).keys with length := 0 },
          values := { (Spec.metadataHeader [(hash, value)]).values with length := 0 } },
          remove
            (remove
              (remove raw (mapIndexKey (Spec.metadataHeader [(hash, value)]) hash))
              (vectorKey (Spec.metadataHeader [(hash, value)]).keys 0))
            (vectorKey (Spec.metadataHeader [(hash, value)]).values 0)) := by
    simp [mapRemove, Spec.metadataHeader, initialMap, mapIndexKey, vectorKey,
      hindex, hdecode, hkeys, hvalues, hmetadata, mapLength,
      load, erase, require, expect, Bind.bind, Pure.pure,
      Tx.run_bind, Tx.bind, Tx.run, Except.bind]
  simpa [singletonMetadataRemovedRaw, Spec.metadataHeader, initialMap,
    mapIndexKey, vectorKey] using hrun

def singletonMetadataDeletedRaw (raw : Raw) (hash : Hash) : Raw :=
  write (singletonMetadataRemovedRaw raw hash) metadataKey
    (Borsh.encodeMap (Spec.metadataHeader []))

theorem singleton_metadata_delete_entry (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader) (hash : Hash) (value : Metadata)
    (layout : Spec.MetadataLayout raw [(hash, value)])
    (hbounded : Spec.MetadataBounded value)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.deleteMetadata hash) =
      .ok ⟨singletonMetadataDeletedRaw raw hash, [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader [(hash, value)])) =
      some (Spec.metadataHeader [(hash, value)]) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
  have hremove := singleton_metadata_remove raw hash value layout hbounded
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, loadMap, layout.header, hmap, hremove, singletonMetadataDeletedRaw,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem singleton_metadata_delete_establishes_empty_layout (raw : Raw)
    (hash : Hash) (value : Metadata)
    (layout : Spec.MetadataLayout raw [(hash, value)]) :
    Spec.MetadataLayout (singletonMetadataDeletedRaw raw hash) [] := by
  constructor
  · simp
  · exact read_write_self _ _ _
  · intro query
    have hheader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
    have hvalue : mapIndexKey initialMap query ≠ vectorKey initialMap.values 0 := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, vectorKey, initialMap, query.property] at hlen
    have hkey : mapIndexKey initialMap query ≠ vectorKey initialMap.keys 0 := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, vectorKey, initialMap, query.property] at hlen
    unfold singletonMetadataDeletedRaw singletonMetadataRemovedRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_remove_other _ _ _ hvalue]
    rw [read_remove_other _ _ _ hkey]
    by_cases hq : query = hash
    · subst query
      simp [read_remove_self, Spec.findHash]
    · have hnotIndex : mapIndexKey initialMap query ≠ mapIndexKey initialMap hash := by
        intro he
        exact hq (canonical_map_index_injective query hash he)
      rw [read_remove_other _ _ _ hnotIndex]
      have hnotVal : hash.val ≠ query.val := by
        intro he
        exact hq (Subtype.ext he.symm)
      simpa [Spec.findHash, hnotVal] using layout.index query
  · intro index hindex
    simp at hindex
  · intro index hindex
    simp at hindex

theorem singleton_metadata_delete_preserves_state (raw : Raw)
    (hash : Hash) :
    read (singletonMetadataDeletedRaw raw hash) stateKey = read raw stateKey := by
  have hheader : stateKey ≠ metadataKey := by decide
  have hvalue : stateKey ≠ vectorKey initialMap.values 0 := by decide
  have hkey : stateKey ≠ vectorKey initialMap.keys 0 := by decide
  have hindex : stateKey ≠ mapIndexKey initialMap hash := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, hash.property] at hlen
  unfold singletonMetadataDeletedRaw singletonMetadataRemovedRaw
  rw [read_write_other _ _ _ _ hheader]
  rw [read_remove_other _ _ _ hvalue]
  rw [read_remove_other _ _ _ hkey]
  rw [read_remove_other _ _ _ hindex]

theorem singleton_metadata_delete_then_get (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader) (hash : Hash) (value : Metadata)
    (layout : Spec.MetadataLayout raw [(hash, value)])
    (hbounded : Spec.MetadataBounded value)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata hash) = .ok out) :
    step cfg out.raw env .getMetadata = .ok ⟨out.raw, [], .metadata []⟩ := by
  rw [singleton_metadata_delete_entry cfg raw env setHeader hash value layout
    hbounded hstate hsetIndex hsetLength hsetPrefix howner] at hstep
  cases hstep
  have hstate' : read (singletonMetadataDeletedRaw raw hash) stateKey =
      some (Borsh.encodeSet setHeader) := by
    rw [singleton_metadata_delete_preserves_state]
    exact hstate
  apply metadata_getter_matches_layout cfg _ env setHeader [] hstate'
    hsetIndex hsetLength hsetPrefix
  · exact singleton_metadata_delete_establishes_empty_layout raw hash value layout
  · simp
  · intro entry hentry
    simp at hentry

end SputnikFactory
