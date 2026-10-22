import Proofs.MetadataMalformed

namespace SputnikFactory

/-- Exact raw writes performed when a second distinct metadata hash is added
to a one-entry legacy `UnorderedMap`. -/
def secondMetadataBodyRaw (raw : Raw) (hash : Hash) (value : Metadata) : Raw :=
  write
    (write
      (write raw (mapIndexKey initialMap hash) (leBytes 8 1))
      (vectorKey initialMap.keys 1) hash.val)
    (vectorKey initialMap.values 1) (Borsh.encodeMetadata value)

def secondMetadataRaw (raw : Raw) (firstHash hash : Hash)
    (firstValue value : Metadata) : Raw :=
  write (secondMetadataBodyRaw raw hash value) metadataKey
    (Borsh.encodeMap (Spec.metadataHeader [(firstHash, firstValue), (hash, value)]))

theorem second_metadata_insert (raw : Raw) (firstHash hash : Hash)
    (firstValue value : Metadata)
    (habsent : read raw (mapIndexKey initialMap hash) = none) :
    (mapInsert (Spec.metadataHeader [(firstHash, firstValue)]) hash value).run raw =
      .ok (Spec.metadataHeader [(firstHash, firstValue), (hash, value)],
        secondMetadataBodyRaw raw hash value) := by
  have habsent' : read raw
      (mapIndexKey (Spec.metadataHeader [(firstHash, firstValue)]) hash) = none := by
    simpa [Spec.metadataHeader, mapIndexKey] using habsent
  have hrun :
      (mapInsert (Spec.metadataHeader [(firstHash, firstValue)]) hash value).run raw =
        .ok ({ Spec.metadataHeader [(firstHash, firstValue)] with
          keys := { (Spec.metadataHeader [(firstHash, firstValue)]).keys with length := 2 },
          values := { (Spec.metadataHeader [(firstHash, firstValue)]).values with length := 2 } },
          write
            (write
              (write raw
                (mapIndexKey (Spec.metadataHeader [(firstHash, firstValue)]) hash)
                (leBytes 8 1))
              (vectorKey (Spec.metadataHeader [(firstHash, firstValue)]).keys 1) hash.val)
            (vectorKey (Spec.metadataHeader [(firstHash, firstValue)]).values 1)
            (Borsh.encodeMetadata value)) := by
    simp [mapInsert, habsent', mapLength, vectorPush, load, save, require,
      Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind, u64Bound]
    simp [Spec.metadataHeader, initialMap, Tx.run]
  simpa [secondMetadataBodyRaw, Spec.metadataHeader, initialMap, mapIndexKey,
    vectorKey] using hrun

/-- The exported owner-only method appends the second metadata entry and saves
the length-two map header. -/
theorem second_metadata_entry (cfg : Config) (raw : Raw) (env : Env)
    (setHeader : SetHeader) (firstHash hash : Hash)
    (firstValue value : Metadata) (code : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = some
      (Borsh.encodeMap (Spec.metadataHeader [(firstHash, firstValue)])))
    (habsent : read raw (mapIndexKey initialMap hash) = none) :
    step cfg raw env (.storeMetadata hash value false) =
      .ok ⟨write (secondMetadataBodyRaw raw hash value) metadataKey
        (Borsh.encodeMap (Spec.metadataHeader [(firstHash, firstValue), (hash, value)])),
        [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader [(firstHash, firstValue)])) =
      some (Spec.metadataHeader [(firstHash, firstValue)]) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
  have hinsert := second_metadata_insert raw firstHash hash firstValue value habsent
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hcode, hmetadata, hmap, hinsert, Call.private, Call.rejectDeposit,
    Call.isNew, Call.ownerOnly, Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem second_metadata_distinct (raw : Raw) (firstHash hash : Hash)
    (firstValue : Metadata)
    (layout : Spec.MetadataLayout raw [(firstHash, firstValue)])
    (habsent : read raw (mapIndexKey initialMap hash) = none) :
    firstHash ≠ hash := by
  intro he
  subst hash
  have hfirst := layout.index firstHash
  simp [Spec.findHash] at hfirst
  rw [hfirst] at habsent
  contradiction

theorem second_metadata_layout (raw : Raw) (firstHash hash : Hash)
    (firstValue value : Metadata)
    (layout : Spec.MetadataLayout raw [(firstHash, firstValue)])
    (habsent : read raw (mapIndexKey initialMap hash) = none) :
    Spec.MetadataLayout (secondMetadataRaw raw firstHash hash firstValue value)
      [(firstHash, firstValue), (hash, value)] := by
  have hdistinct := second_metadata_distinct raw firstHash hash firstValue layout habsent
  have hdistinctVal : firstHash.val ≠ hash.val := by
    intro he
    exact hdistinct (Subtype.ext he)
  constructor
  · simp [hdistinct]
  · exact read_write_self _ _ _
  · intro query
    have hheader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
    have hvalue : mapIndexKey initialMap query ≠ vectorKey initialMap.values 1 := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, vectorKey, initialMap, query.property] at hlen
    have hkey : mapIndexKey initialMap query ≠ vectorKey initialMap.keys 1 := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, vectorKey, initialMap, query.property] at hlen
    unfold secondMetadataRaw secondMetadataBodyRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_write_other _ _ _ _ hvalue]
    rw [read_write_other _ _ _ _ hkey]
    by_cases hq : query = hash
    · subst query
      simp [Spec.findHash, hdistinctVal, read_write_self]
    · have hnotIndex : mapIndexKey initialMap query ≠ mapIndexKey initialMap hash := by
        intro he
        exact hq (canonical_map_index_injective query hash he)
      have hnotVal : hash.val ≠ query.val := by
        intro he
        exact hq (Subtype.ext he.symm)
      rw [read_write_other _ _ _ _ hnotIndex]
      simpa [Spec.findHash, hnotVal] using layout.index query
  · intro index hindex
    have hindex2 : index < 2 := by simpa using hindex
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with hzero | hone
    · subst index
      have hheader : vectorKey initialMap.keys 0 ≠ metadataKey := by decide
      have hvalue : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.values 1 := by decide
      have hkey : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.keys 1 := by decide
      have hindexKey : vectorKey initialMap.keys 0 ≠ mapIndexKey initialMap hash := by
        intro he
        have hlen := congrArg List.length he
        simp [mapIndexKey, vectorKey, initialMap, hash.property] at hlen
      unfold secondMetadataRaw secondMetadataBodyRaw
      rw [read_write_other _ _ _ _ hheader]
      rw [read_write_other _ _ _ _ hvalue]
      rw [read_write_other _ _ _ _ hkey]
      rw [read_write_other _ _ _ _ hindexKey]
      simpa using layout.key 0 (by simp)
    · subst index
      have hheader : vectorKey initialMap.keys 1 ≠ metadataKey := by decide
      have hvalue : vectorKey initialMap.keys 1 ≠ vectorKey initialMap.values 1 := by decide
      unfold secondMetadataRaw secondMetadataBodyRaw
      rw [read_write_other _ _ _ _ hheader]
      rw [read_write_other _ _ _ _ hvalue]
      simp [read_write_self]
  · intro index hindex
    have hindex2 : index < 2 := by simpa using hindex
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with hzero | hone
    · subst index
      have hheader : vectorKey initialMap.values 0 ≠ metadataKey := by decide
      have hvalue : vectorKey initialMap.values 0 ≠ vectorKey initialMap.values 1 := by decide
      have hkey : vectorKey initialMap.values 0 ≠ vectorKey initialMap.keys 1 := by decide
      have hindexKey : vectorKey initialMap.values 0 ≠ mapIndexKey initialMap hash := by
        intro he
        have hlen := congrArg List.length he
        simp [mapIndexKey, vectorKey, initialMap, hash.property] at hlen
      unfold secondMetadataRaw secondMetadataBodyRaw
      rw [read_write_other _ _ _ _ hheader]
      rw [read_write_other _ _ _ _ hvalue]
      rw [read_write_other _ _ _ _ hkey]
      rw [read_write_other _ _ _ _ hindexKey]
      simpa using layout.value 0 (by simp)
    · subst index
      have hheader : vectorKey initialMap.values 1 ≠ metadataKey := by decide
      unfold secondMetadataRaw secondMetadataBodyRaw
      rw [read_write_other _ _ _ _ hheader]
      simp [read_write_self]

theorem second_metadata_entry_establishes_layout
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (firstHash hash : Hash) (firstValue value : Metadata) (code : Bytes)
    (layout : Spec.MetadataLayout raw [(firstHash, firstValue)])
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash value false) = .ok out) :
    Spec.MetadataLayout out.raw [(firstHash, firstValue), (hash, value)] := by
  rw [second_metadata_entry cfg raw env setHeader firstHash hash firstValue value
    code hstate hsetIndex hsetLength hsetPrefix howner hcode layout.header habsent]
    at hstep
  cases hstep
  exact second_metadata_layout raw firstHash hash firstValue value layout habsent

theorem second_metadata_write_preserves_state (raw : Raw)
    (firstHash hash : Hash) (firstValue value : Metadata) :
    read (secondMetadataRaw raw firstHash hash firstValue value) stateKey =
      read raw stateKey := by
  have hheader : stateKey ≠ metadataKey := by decide
  have hvalue : stateKey ≠ vectorKey initialMap.values 1 := by decide
  have hkey : stateKey ≠ vectorKey initialMap.keys 1 := by decide
  have hindex : stateKey ≠ mapIndexKey initialMap hash := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, hash.property] at hlen
  unfold secondMetadataRaw secondMetadataBodyRaw
  rw [read_write_other _ _ _ _ hheader]
  rw [read_write_other _ _ _ _ hvalue]
  rw [read_write_other _ _ _ _ hkey]
  rw [read_write_other _ _ _ _ hindex]

theorem second_metadata_store_then_get
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (firstHash hash : Hash) (firstValue value : Metadata) (code : Bytes)
    (layout : Spec.MetadataLayout raw [(firstHash, firstValue)])
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hboundedFirst : Spec.MetadataBounded firstValue)
    (hboundedNew : Spec.MetadataBounded value)
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash value false) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata [(firstHash, firstValue), (hash, value)]⟩ := by
  rw [second_metadata_entry cfg raw env setHeader firstHash hash firstValue value
    code hstate hsetIndex hsetLength hsetPrefix howner hcode layout.header habsent]
    at hstep
  cases hstep
  have hstate' : read (secondMetadataRaw raw firstHash hash firstValue value)
      stateKey = some (Borsh.encodeSet setHeader) := by
    rw [second_metadata_write_preserves_state]
    exact hstate
  apply metadata_getter_matches_layout cfg _ env setHeader
    [(firstHash, firstValue), (hash, value)] hstate' hsetIndex hsetLength
    hsetPrefix
  · exact second_metadata_layout raw firstHash hash firstValue value
      layout habsent
  · simp
  · intro entry hentry
    simp at hentry
    rcases hentry with he | he
    · subst entry
      exact hboundedFirst
    · subst entry
      exact hboundedNew

end SputnikFactory
