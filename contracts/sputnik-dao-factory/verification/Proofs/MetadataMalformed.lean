import Proofs.MetadataInsert

namespace SputnikFactory

theorem vector_replace_present (header : VectorHeader) (raw : Raw)
    (index : Nat) (previous replacement : Bytes)
    (hindex : index < header.length)
    (hread : read raw (vectorKey header index) = some previous) :
    (vectorReplace header index replacement).run raw =
      .ok (previous, write raw (vectorKey header index) replacement) := by
  simp [vectorReplace, hindex, hread, require, expect, load, save,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- Existing metadata replacement works at any valid map index. The SDK
deserializes the old value before returning its unchanged header. -/
theorem valid_metadata_replacement_general (raw : Raw) (header : MapHeader)
    (hash : Hash) (index : Nat) (previous replacement : Metadata)
    (hindex : read raw (mapIndexKey header hash) =
      some (leBytes 8 index))
    (hindexBound : index < 256 ^ 8)
    (hvectorBound : index < header.values.length)
    (hvalue : read raw (vectorKey header.values index) =
      some (Borsh.encodeMetadata previous))
    (hbounded : Spec.MetadataBounded previous) :
    (mapInsert header hash replacement).run raw =
      .ok (header, write raw (vectorKey header.values index)
        (Borsh.encodeMetadata replacement)) := by
  have hdecode := exact_natural_encode 8 index hindexBound
  have hreplace := vector_replace_present header.values raw index
    (Borsh.encodeMetadata previous) (Borsh.encodeMetadata replacement)
    hvectorBound hvalue
  have hprev := exact_metadata_encode_bounded previous hbounded.1 hbounded.2
  simp [mapInsert, hindex, hdecode, hreplace, hprev,
    expect, load, Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run,
    Except.bind]

theorem store_metadata_valid_replacement_general
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (index : Nat)
    (previous replacement : Metadata) (code : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = some
      (Borsh.encodeMap (Spec.metadataHeader order)))
    (horderLength : order.length < 256 ^ 8)
    (hindex : read raw (mapIndexKey initialMap hash) =
      some (leBytes 8 index))
    (hvectorBound : index < order.length)
    (hvalue : read raw (vectorKey initialMap.values index) =
      some (Borsh.encodeMetadata previous))
    (hbounded : Spec.MetadataBounded previous) :
    step cfg raw env (.storeMetadata hash replacement false) =
      .ok ⟨write
        (write raw (vectorKey initialMap.values index)
          (Borsh.encodeMetadata replacement))
        metadataKey (Borsh.encodeMap (Spec.metadataHeader order)),
        [], .unit⟩ := by
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
  have hindex' : read raw
      (mapIndexKey (Spec.metadataHeader order) hash) =
      some (leBytes 8 index) := by
    simpa [Spec.metadataHeader, mapIndexKey] using hindex
  have hvalue' : read raw
      (vectorKey (Spec.metadataHeader order).values index) =
      some (Borsh.encodeMetadata previous) := by
    simpa [Spec.metadataHeader, vectorKey] using hvalue
  have hvectorBound' : index < (Spec.metadataHeader order).values.length := by
    simpa [Spec.metadataHeader] using hvectorBound
  have hindexBound : index < 256 ^ 8 := Nat.lt_trans hvectorBound horderLength
  have hreplace := valid_metadata_replacement_general raw
    (Spec.metadataHeader order) hash index previous replacement hindex'
    hindexBound hvectorBound' hvalue' hbounded
  have hrun :
      step cfg raw env (.storeMetadata hash replacement false) =
        .ok ⟨write
          (write raw (vectorKey (Spec.metadataHeader order).values index)
            (Borsh.encodeMetadata replacement))
          metadataKey (Borsh.encodeMap (Spec.metadataHeader order)),
          [], .unit⟩ := by
    simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
      body, hcode, hmetadata, hmap, hreplace, Call.private, Call.rejectDeposit,
      Call.isNew, Call.ownerOnly, Call.saveHeader, require, expect, done, load, save,
      Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]
  simpa [Spec.metadataHeader, vectorKey] using hrun

/-- A legacy map can have a valid index and vector header but an invalid old
value. SDK `insert` deserializes the evicted value even when its Rust caller
ignores it, so replacement aborts after a provisional storage write. -/
def malformedPreviousValue (hash : Hash) : Raw :=
  write
    (write [] (mapIndexKey initialMap hash) (leBytes 8 0))
    (vectorKey initialMap.values 0) [0]

theorem malformed_metadata_replacement_aborts
    (raw : Raw) (hash : Hash) (replacement : Metadata)
    (hindex : read raw (mapIndexKey initialMap hash) = some (leBytes 8 0))
    (hvalue : read raw (vectorKey initialMap.values 0) = some [0]) :
    (mapInsert (Spec.metadataHeader [(hash, replacement)]) hash replacement).run raw =
      .error .invalidMetadata := by
  have hdecode : Borsh.exact (Borsh.natural 8) (leBytes 8 0) = some 0 := by decide
  have hbad : Borsh.exact Borsh.metadata [0] = none := by decide
  have hindex' : read raw
      (mapIndexKey (Spec.metadataHeader [(hash, replacement)]) hash) =
      some (leBytes 8 0) := by
    simpa [Spec.metadataHeader, mapIndexKey] using hindex
  have hvalue' : read raw
      (vectorKey (Spec.metadataHeader [(hash, replacement)]).values 0) =
      some [0] := by
    simpa [Spec.metadataHeader, vectorKey] using hvalue
  have hlen : 0 < (Spec.metadataHeader [(hash, replacement)]).values.length := by
    simp [Spec.metadataHeader]
  have hreplace := vector_replace_present
    (Spec.metadataHeader [(hash, replacement)]).values
    raw 0 [0] (Borsh.encodeMetadata replacement)
    hlen hvalue'
  simp [mapInsert, hindex', hdecode, hreplace, hbad,
    expect, load, Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

/-- A valid old value is decoded even though the caller discards it. When it
decodes, replacement changes only the value vector record; the header stays
at length one. -/
theorem valid_metadata_replacement (raw : Raw) (hash : Hash)
    (previous replacement : Metadata)
    (hindex : read raw (mapIndexKey initialMap hash) = some (leBytes 8 0))
    (hvalue : read raw (vectorKey initialMap.values 0) =
      some (Borsh.encodeMetadata previous))
    (hbounded : Spec.MetadataBounded previous) :
    (mapInsert (Spec.metadataHeader [(hash, previous)]) hash replacement).run raw =
      .ok (Spec.metadataHeader [(hash, previous)],
        write raw (vectorKey initialMap.values 0) (Borsh.encodeMetadata replacement)) := by
  have hdecode : Borsh.exact (Borsh.natural 8) (leBytes 8 0) = some 0 := by decide
  have hindex' : read raw
      (mapIndexKey (Spec.metadataHeader [(hash, previous)]) hash) =
      some (leBytes 8 0) := by
    simpa [Spec.metadataHeader, mapIndexKey] using hindex
  have hvalue' : read raw
      (vectorKey (Spec.metadataHeader [(hash, previous)]).values 0) =
      some (Borsh.encodeMetadata previous) := by
    simpa [Spec.metadataHeader, vectorKey] using hvalue
  have hlen : 0 < (Spec.metadataHeader [(hash, previous)]).values.length := by
    simp [Spec.metadataHeader]
  have hreplace := vector_replace_present
    (Spec.metadataHeader [(hash, previous)]).values raw 0
    (Borsh.encodeMetadata previous) (Borsh.encodeMetadata replacement)
    hlen hvalue'
  have hprev := exact_metadata_encode_bounded previous hbounded.1 hbounded.2
  have hrun :
      (mapInsert (Spec.metadataHeader [(hash, previous)]) hash replacement).run raw =
        .ok (Spec.metadataHeader [(hash, previous)],
          write raw (vectorKey (Spec.metadataHeader [(hash, previous)]).values 0)
            (Borsh.encodeMetadata replacement)) := by
    simp [mapInsert, hindex', hdecode, hreplace, hprev,
      expect, load, Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]
  simpa [Spec.metadataHeader, vectorKey] using hrun

theorem store_metadata_valid_replacement
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (hash : Hash) (previous replacement : Metadata) (code : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = some
      (Borsh.encodeMap (Spec.metadataHeader [(hash, previous)])))
    (hindex : read raw (mapIndexKey initialMap hash) = some (leBytes 8 0))
    (hvalue : read raw (vectorKey initialMap.values 0) =
      some (Borsh.encodeMetadata previous))
    (hbounded : Spec.MetadataBounded previous) :
    step cfg raw env (.storeMetadata hash replacement false) =
      .ok ⟨write
        (write raw (vectorKey initialMap.values 0) (Borsh.encodeMetadata replacement))
        metadataKey (Borsh.encodeMap (Spec.metadataHeader [(hash, previous)])),
        [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader [(hash, previous)])) =
      some (Spec.metadataHeader [(hash, previous)]) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
  have hreplace := valid_metadata_replacement raw hash previous replacement
    hindex hvalue hbounded
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hcode, hmetadata, hmap, hreplace, Call.private, Call.rejectDeposit,
    Call.isNew, Call.ownerOnly, Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

/-- Replacing the sole metadata value preserves the exact map-index and vector
layout used by the exported getter. The header is resaved with length one. -/
theorem singleton_metadata_replacement_preserves_layout
    (raw : Raw) (hash : Hash) (previous replacement : Metadata)
    (layout : Spec.MetadataLayout raw [(hash, previous)]) :
    Spec.MetadataLayout
      (write
        (write raw (vectorKey initialMap.values 0) (Borsh.encodeMetadata replacement))
        metadataKey (Borsh.encodeMap (Spec.metadataHeader [(hash, previous)])))
      [(hash, replacement)] := by
  have hheader : metadataKey ≠ vectorKey initialMap.values 0 := by decide
  have hsame : Spec.metadataHeader [(hash, previous)] =
      Spec.metadataHeader [(hash, replacement)] := rfl
  constructor
  · simp
  · rw [read_write_self]
    exact congrArg (fun h => some (Borsh.encodeMap h)) hsame
  · intro query
    have hnotHeader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
    have hnotValue : mapIndexKey initialMap query ≠ vectorKey initialMap.values 0 := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, vectorKey, initialMap, query.property] at hlen
    rw [read_write_other _ _ _ _ hnotHeader]
    rw [read_write_other _ _ _ _ hnotValue]
    simpa [Spec.findHash] using layout.index query
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hnotHeader : vectorKey initialMap.keys 0 ≠ metadataKey := by decide
    have hnotValue : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.values 0 := by decide
    rw [read_write_other _ _ _ _ hnotHeader]
    rw [read_write_other _ _ _ _ hnotValue]
    simpa using layout.key 0 (by simp)
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hnotHeader : vectorKey initialMap.values 0 ≠ metadataKey := by decide
    rw [read_write_other _ _ _ _ hnotHeader]
    simp [read_write_self]

theorem store_metadata_valid_replacement_preserves_layout
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (hash : Hash) (previous replacement : Metadata) (code : Bytes)
    (layout : Spec.MetadataLayout raw [(hash, previous)])
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hbounded : Spec.MetadataBounded previous)
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash replacement false) = .ok out) :
    Spec.MetadataLayout out.raw [(hash, replacement)] := by
  have hindex : read raw (mapIndexKey initialMap hash) = some (leBytes 8 0) := by
    simpa [Spec.findHash] using layout.index hash
  have hvalue : read raw (vectorKey initialMap.values 0) =
      some (Borsh.encodeMetadata previous) := by
    simpa using layout.value 0 (by simp)
  rw [store_metadata_valid_replacement cfg raw env setHeader hash previous
    replacement code hstate hsetIndex hsetLength hsetPrefix howner hcode
    layout.header hindex hvalue hbounded] at hstep
  cases hstep
  exact singleton_metadata_replacement_preserves_layout raw hash previous
    replacement layout

theorem store_metadata_replacement_then_get
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (hash : Hash) (previous replacement : Metadata) (code : Bytes)
    (layout : Spec.MetadataLayout raw [(hash, previous)])
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hboundedPrevious : Spec.MetadataBounded previous)
    (hboundedReplacement : Spec.MetadataBounded replacement)
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash replacement false) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata [(hash, replacement)]⟩ := by
  have hindex : read raw (mapIndexKey initialMap hash) = some (leBytes 8 0) := by
    simpa [Spec.findHash] using layout.index hash
  have hvalue : read raw (vectorKey initialMap.values 0) =
      some (Borsh.encodeMetadata previous) := by
    simpa using layout.value 0 (by simp)
  rw [store_metadata_valid_replacement cfg raw env setHeader hash previous
    replacement code hstate hsetIndex hsetLength hsetPrefix howner hcode
    layout.header hindex hvalue hboundedPrevious] at hstep
  cases hstep
  have hstate' : read
      (write
        (write raw (vectorKey initialMap.values 0) (Borsh.encodeMetadata replacement))
        metadataKey (Borsh.encodeMap (Spec.metadataHeader [(hash, previous)])))
      stateKey = some (Borsh.encodeSet setHeader) := by
    have hneHeader : stateKey ≠ metadataKey := by decide
    have hneValue : stateKey ≠ vectorKey initialMap.values 0 := by decide
    rw [read_write_other _ _ _ _ hneHeader]
    rw [read_write_other _ _ _ _ hneValue]
    exact hstate
  apply metadata_getter_matches_layout cfg _ env setHeader [(hash, replacement)]
    hstate' hsetIndex hsetLength hsetPrefix
  · exact singleton_metadata_replacement_preserves_layout raw hash previous
      replacement layout
  · simp
  · intro entry hentry
    simp at hentry
    subst entry
    exact hboundedReplacement

theorem malformed_previous_metadata_replacement_aborts
    (hash : Hash) (replacement : Metadata) :
    (mapInsert (Spec.metadataHeader [(hash, replacement)]) hash replacement).run
      (malformedPreviousValue hash) = .error .invalidMetadata := by
  have hseparate : mapIndexKey initialMap hash ≠ vectorKey initialMap.values 0 := by
    intro he
    have hlen := congrArg List.length he
    simp [mapIndexKey, vectorKey, initialMap, hash.property] at hlen
  have hindex : read (malformedPreviousValue hash) (mapIndexKey initialMap hash) =
      some (leBytes 8 0) := by
    unfold malformedPreviousValue
    rw [read_write_other _ _ _ _ hseparate]
    exact read_write_self _ _ _
  have hvalue : read (malformedPreviousValue hash) (vectorKey initialMap.values 0) =
      some [0] := read_write_self _ _ _
  exact malformed_metadata_replacement_aborts _ hash replacement hindex hvalue

/-- The exported owner-only call reaches the SDK map operation and aborts when
the old value record is malformed. The model commits no provisional writes. -/
theorem store_metadata_malformed_previous_aborts
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (hash : Hash) (replacement : Metadata) (setDefault : Bool) (code : Bytes)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hmetadata : read raw metadataKey = some
      (Borsh.encodeMap (Spec.metadataHeader [(hash, replacement)])))
    (hindex : read raw (mapIndexKey initialMap hash) = some (leBytes 8 0))
    (hvalue : read raw (vectorKey initialMap.values 0) = some [0]) :
    step cfg raw env (.storeMetadata hash replacement setDefault) =
      .error .invalidMetadata := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader [(hash, replacement)])) =
      some (Spec.metadataHeader [(hash, replacement)]) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
    · simp [Spec.metadataHeader]
    · simp [Spec.metadataHeader, initialMap]
  have habort := malformed_metadata_replacement_aborts raw hash replacement hindex hvalue
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hcode, hmetadata, hmap, habort, Call.private, Call.rejectDeposit,
    Call.isNew, Call.ownerOnly, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

end SputnikFactory
