import Proofs.StorageProjection

namespace SputnikFactory

def firstMetadataBodyRawOn (raw : Raw) (hash : Hash) (value : Metadata) : Raw :=
  write
    (write
      (write raw (mapIndexKey initialMap hash) (leBytes 8 0))
      (vectorKey initialMap.keys 0) hash.val)
    (vectorKey initialMap.values 0) (Borsh.encodeMetadata value)

def firstMetadataRawOn (raw : Raw) (hash : Hash) (value : Metadata) : Raw :=
  write (firstMetadataBodyRawOn raw hash value) metadataKey
    (Borsh.encodeMap (Spec.metadataHeader [(hash, value)]))

def firstMetadataBodyRaw (hash : Hash) (value : Metadata) : Raw :=
  firstMetadataBodyRawOn [] hash value

def firstMetadataRaw (hash : Hash) (value : Metadata) : Raw :=
  firstMetadataRawOn [] hash value

/-- The SDK's first insertion creates an index and parallel key/value vector
records, with an incremented header. -/
theorem first_metadata_insert (hash : Hash) (value : Metadata) :
    (mapInsert initialMap hash value).run [] =
      .ok (Spec.metadataHeader [(hash, value)], firstMetadataBodyRaw hash value) := by
  rfl

theorem first_metadata_insert_on (raw : Raw) (hash : Hash) (value : Metadata)
    (habsent : read raw (mapIndexKey initialMap hash) = none) :
    (mapInsert initialMap hash value).run raw =
      .ok (Spec.metadataHeader [(hash, value)],
        firstMetadataBodyRawOn raw hash value) := by
  simp [mapInsert, mapLength, vectorPush, firstMetadataBodyRawOn,
    Spec.metadataHeader, habsent, load, save, require,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]
  simp [initialMap, u64Bound, Tx.bind, Tx.run]

theorem canonical_map_index_injective (left right : Hash)
    (h : mapIndexKey initialMap left = mapIndexKey initialMap right) :
    left = right := by
  apply Subtype.ext
  change initialMap.indexPrefix ++ left.val = initialMap.indexPrefix ++ right.val at h
  exact List.append_cancel_left h

theorem first_metadata_layout_on (raw : Raw) (hash : Hash) (value : Metadata)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none) :
    Spec.MetadataLayout (firstMetadataRawOn raw hash value) [(hash, value)] := by
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
    by_cases he : query = hash
    · subst query
      unfold firstMetadataRawOn firstMetadataBodyRawOn
      rw [read_write_other _ _ _ _ hheader]
      rw [read_write_other _ _ _ _ hvalue]
      rw [read_write_other _ _ _ _ hkey]
      simp [Spec.findHash, read_write_self]
    · have hindex : mapIndexKey initialMap query ≠ mapIndexKey initialMap hash := by
        intro hkeys
        exact he (canonical_map_index_injective query hash hkeys)
      have hval : hash.val ≠ query.val := by
        intro hv
        exact he (Subtype.ext hv.symm)
      unfold firstMetadataRawOn firstMetadataBodyRawOn
      rw [read_write_other _ _ _ _ hheader]
      rw [read_write_other _ _ _ _ hvalue]
      rw [read_write_other _ _ _ _ hkey]
      rw [read_write_other _ _ _ _ hindex]
      simp [Spec.findHash, hval, hindexes query]
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hheader : vectorKey initialMap.keys 0 ≠ metadataKey := by decide
    have hvalue : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.values 0 := by decide
    simp [firstMetadataRawOn, firstMetadataBodyRawOn, read_write_other,
      hheader, hvalue, read_write_self]
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hheader : vectorKey initialMap.values 0 ≠ metadataKey := by decide
    simp [firstMetadataRawOn, firstMetadataBodyRawOn, read_write_other,
      hheader, read_write_self]

theorem first_metadata_layout (hash : Hash) (value : Metadata) :
    Spec.MetadataLayout (firstMetadataRaw hash value) [(hash, value)] := by
  exact first_metadata_layout_on [] hash value (fun _ => rfl)

/-- First exported metadata insertion, before optional default selection. -/
theorem first_metadata_entry (cfg : Config) (raw : Raw) (env : Env)
    (setHeader : SetHeader) (hash : Hash) (value : Metadata) (code : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = none)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none) :
    step cfg raw env (.storeMetadata hash value false) =
      .ok ⟨firstMetadataRawOn raw hash value, [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hinsert := first_metadata_insert_on raw hash value (hindexes hash)
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hcode, hmetadata, Call.private, Call.rejectDeposit,
    Call.isNew, Call.ownerOnly, Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, hinsert, Tx.bind, Tx.run, Except.bind,
    firstMetadataRawOn]

theorem first_metadata_entry_establishes_layout (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader) (hash : Hash) (value : Metadata)
    (code : Bytes) (out : Outcome)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = none)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none)
    (hstep : step cfg raw env (.storeMetadata hash value false) = .ok out) :
    Spec.MetadataLayout out.raw [(hash, value)] := by
  rw [first_metadata_entry cfg raw env setHeader hash value code hstate
    hsetIndex hsetLength hsetPrefix howner hcode hmetadata hindexes] at hstep
  cases hstep
  exact first_metadata_layout_on raw hash value hindexes

theorem metadata_layout_after_default_selection (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash)
    (layout : Spec.MetadataLayout raw order) :
    Spec.MetadataLayout (write raw defaultKey hash.val) order := by
  constructor
  · exact layout.unique
  · have hne : metadataKey ≠ defaultKey := by decide
    rw [read_write_other raw defaultKey metadataKey hash.val hne]
    exact layout.header
  · intro query
    have hne : mapIndexKey initialMap query ≠ defaultKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, defaultKey, query.property] at hlen
    rw [read_write_other raw defaultKey _ hash.val hne]
    exact layout.index query
  · intro index hindex
    have hne : vectorKey initialMap.keys index ≠ defaultKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, defaultKey] at hlen
    rw [read_write_other raw defaultKey _ hash.val hne]
    exact layout.key index hindex
  · intro index hindex
    have hne : vectorKey initialMap.values index ≠ defaultKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, defaultKey] at hlen
    rw [read_write_other raw defaultKey _ hash.val hne]
    exact layout.value index hindex

theorem first_metadata_entry_with_default (cfg : Config) (raw : Raw) (env : Env)
    (setHeader : SetHeader) (hash : Hash) (value : Metadata) (code : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = none)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none) :
    step cfg raw env (.storeMetadata hash value true) =
      .ok ⟨write (firstMetadataRawOn raw hash value) defaultKey hash.val,
        [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hinsert := first_metadata_insert_on raw hash value (hindexes hash)
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hcode, hmetadata, Call.private, Call.rejectDeposit,
    Call.isNew, Call.ownerOnly, Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, hinsert, Tx.bind, Tx.run, Except.bind,
    firstMetadataRawOn]

theorem first_metadata_entry_with_default_establishes_layout
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (hash : Hash) (value : Metadata) (code : Bytes) (out : Outcome)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = none)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none)
    (hstep : step cfg raw env (.storeMetadata hash value true) = .ok out) :
    Spec.MetadataLayout out.raw [(hash, value)] := by
  rw [first_metadata_entry_with_default cfg raw env setHeader hash value code
    hstate hsetIndex hsetLength hsetPrefix howner hcode hmetadata hindexes] at hstep
  cases hstep
  exact metadata_layout_after_default_selection _ _ hash
    (first_metadata_layout_on raw hash value hindexes)

theorem first_metadata_write_preserves_state (raw : Raw) (hash : Hash)
    (value : Metadata) :
    read (firstMetadataRawOn raw hash value) stateKey = read raw stateKey := by
  have hheader : stateKey ≠ metadataKey := by decide
  have hvalue : stateKey ≠ vectorKey initialMap.values 0 := by decide
  have hkey : stateKey ≠ vectorKey initialMap.keys 0 := by decide
  have hindex : stateKey ≠ mapIndexKey initialMap hash := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, hash.property] at hlen
  unfold firstMetadataRawOn firstMetadataBodyRawOn
  rw [read_write_other _ _ _ _ hheader]
  rw [read_write_other _ _ _ _ hvalue]
  rw [read_write_other _ _ _ _ hkey]
  rw [read_write_other _ _ _ _ hindex]

theorem first_metadata_getter_roundtrip (cfg : Config) (raw : Raw) (env : Env)
    (setHeader : SetHeader) (hash : Hash) (value : Metadata)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none)
    (hbounded : Spec.MetadataBounded value) :
    step cfg (firstMetadataRawOn raw hash value) env .getMetadata =
      .ok ⟨firstMetadataRawOn raw hash value, [], .metadata [(hash, value)]⟩ := by
  apply metadata_getter_matches_layout cfg _ env setHeader [(hash, value)]
  · rw [first_metadata_write_preserves_state]
    exact hstate
  · exact hsetIndex
  · exact hsetLength
  · exact hsetPrefix
  · exact first_metadata_layout_on raw hash value hindexes
  · simp
  · intro entry hentry
    simp at hentry
    subst entry
    exact hbounded

theorem first_metadata_store_then_get (cfg : Config) (raw : Raw) (env : Env)
    (setHeader : SetHeader) (hash : Hash) (value : Metadata)
    (code : Bytes) (out : Outcome)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = none)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none)
    (hbounded : Spec.MetadataBounded value)
    (hstore : step cfg raw env (.storeMetadata hash value false) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata [(hash, value)]⟩ := by
  rw [first_metadata_entry cfg raw env setHeader hash value code hstate
    hsetIndex hsetLength hsetPrefix howner hcode hmetadata hindexes] at hstore
  cases hstore
  exact first_metadata_getter_roundtrip cfg raw env setHeader hash value
    hstate hsetIndex hsetLength hsetPrefix hindexes hbounded

theorem first_metadata_with_default_then_get (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader) (hash : Hash) (value : Metadata)
    (code : Bytes) (out : Outcome)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = none)
    (hindexes : ∀ query, read raw (mapIndexKey initialMap query) = none)
    (hbounded : Spec.MetadataBounded value)
    (hstore : step cfg raw env (.storeMetadata hash value true) = .ok out) :
    read out.raw defaultKey = some hash.val ∧
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata [(hash, value)]⟩ := by
  rw [first_metadata_entry_with_default cfg raw env setHeader hash value code
    hstate hsetIndex hsetLength hsetPrefix howner hcode hmetadata hindexes] at hstore
  cases hstore
  constructor
  · exact read_write_self _ _ _
  · apply metadata_getter_matches_layout cfg _ env setHeader [(hash, value)]
    · rw [read_write_other _ defaultKey stateKey hash.val (by decide)]
      rw [first_metadata_write_preserves_state]
      exact hstate
    · exact hsetIndex
    · exact hsetLength
    · exact hsetPrefix
    · exact metadata_layout_after_default_selection _ _ hash
        (first_metadata_layout_on raw hash value hindexes)
    · simp
    · intro entry hentry
      simp at hentry
      subst entry
      exact hbounded

end SputnikFactory
