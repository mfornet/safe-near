import Proofs.MetadataRemove

namespace SputnikFactory

theorem vector_pop_two (header : VectorHeader) (raw : Raw)
    (last : Bytes) (hlen : header.length = 2)
    (hlast : read raw (vectorKey header 1) = some last) :
    (vectorPop header).run raw =
      .ok (some (last, { header with length := 1 }),
        remove raw (vectorKey header 1)) := by
  simp [vectorPop, hlen, hlast, load, erase, expect,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- The two-element swap-removal case moves index one into index zero, then
deletes index one. It returns the evicted index-zero value for decoding. -/
theorem vector_swap_remove_two_zero (header : VectorHeader) (raw : Raw)
    (first last : Bytes) (hlen : header.length = 2)
    (hfirst : read raw (vectorKey header 0) = some first)
    (hlast : read raw (vectorKey header 1) = some last)
    (hkeys : vectorKey header 0 ≠ vectorKey header 1) :
    (vectorSwapRemove header 0).run raw =
      .ok ((first, { header with length := 1 }),
        write (remove raw (vectorKey header 1)) (vectorKey header 0) last) := by
  have hpop := vector_pop_two header raw last hlen hlast
  have hread : read (remove raw (vectorKey header 1))
      (vectorKey header 0) = some first := by
    rw [read_remove_other _ _ _ hkeys]
    exact hfirst
  have hreplace := vector_replace_present { header with length := 1 }
    (remove raw (vectorKey header 1)) 0 first last (by simp)
    (by simpa [vectorKey] using hread)
  simp [vectorSwapRemove, hlen, hpop, hreplace, require, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]
  simp [vectorKey]

def twoMetadataAfterIndex (raw : Raw) (first second : Hash) : Raw :=
  write (remove raw (mapIndexKey initialMap first))
    (mapIndexKey initialMap second) (leBytes 8 0)

def twoMetadataAfterKeys (raw : Raw) (first second : Hash) : Raw :=
  write
    (remove (twoMetadataAfterIndex raw first second) (vectorKey initialMap.keys 1))
    (vectorKey initialMap.keys 0) second.val

def twoMetadataAfterValues (raw : Raw) (first second : Hash)
    (secondValue : Metadata) : Raw :=
  write
    (remove (twoMetadataAfterKeys raw first second) (vectorKey initialMap.values 1))
    (vectorKey initialMap.values 0) (Borsh.encodeMetadata secondValue)

theorem read_after_index_reassignment (raw : Raw) (first second : Hash)
    (key : Bytes) (value : Bytes)
    (hfirst : key ≠ mapIndexKey initialMap first)
    (hsecond : key ≠ mapIndexKey initialMap second)
    (hread : read raw key = some value) :
    read (twoMetadataAfterIndex raw first second) key = some value := by
  unfold twoMetadataAfterIndex
  rw [read_write_other _ _ _ _ hsecond]
  rw [read_remove_other _ _ _ hfirst]
  exact hread

theorem vector_key_not_metadata_index (header : VectorHeader)
    (index : Nat) (hash : Hash)
    (hprefix : header.keyPrefix.length = 2) :
    vectorKey header index ≠ mapIndexKey initialMap hash := by
  intro he
  have hlen := congrArg List.length he
  simp [vectorKey, mapIndexKey, initialMap, hprefix, hash.property] at hlen

theorem two_metadata_swap_remove (raw : Raw)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)])
    (hbounded : Spec.MetadataBounded firstValue) :
    (mapRemove (Spec.metadataHeader
      [(first, firstValue), (second, secondValue)]) first).run raw =
      .ok (Spec.metadataHeader [(second, secondValue)],
        twoMetadataAfterValues raw first second secondValue) := by
  have hdistinct : first ≠ second := by
    have hu := layout.unique
    simpa using hu
  have hneqval : second.val ≠ first.val := by
    intro he
    exact hdistinct (Subtype.ext he.symm)
  have hindex : read raw (mapIndexKey initialMap first) = some (leBytes 8 0) := by
    simpa [Spec.findHash] using layout.index first
  have hlast : read raw (vectorKey initialMap.keys 1) = some second.val := by
    simpa using layout.key 1 (by simp)
  have hlastGet : (vectorGet (Spec.metadataHeader
      [(first, firstValue), (second, secondValue)]).keys 1).run raw =
      .ok (some second.val, raw) := by
    apply vector_get_present
    · simp [Spec.metadataHeader]
    · simpa [Spec.metadataHeader, vectorKey] using hlast
  have hkey0 : read (twoMetadataAfterIndex raw first second)
      (vectorKey initialMap.keys 0) = some first.val := by
    apply read_after_index_reassignment
    · exact vector_key_not_metadata_index initialMap.keys 0 first (by decide)
    · exact vector_key_not_metadata_index initialMap.keys 0 second (by decide)
    · simpa using layout.key 0 (by simp)
  have hkey1 : read (twoMetadataAfterIndex raw first second)
      (vectorKey initialMap.keys 1) = some second.val := by
    apply read_after_index_reassignment
    · exact vector_key_not_metadata_index initialMap.keys 1 first (by decide)
    · exact vector_key_not_metadata_index initialMap.keys 1 second (by decide)
    · exact hlast
  have hkeys : (vectorSwapRemove (Spec.metadataHeader
      [(first, firstValue), (second, secondValue)]).keys 0).run
        (twoMetadataAfterIndex raw first second) =
      .ok ((first.val, { (Spec.metadataHeader
        [(first, firstValue), (second, secondValue)]).keys with length := 1 }),
        twoMetadataAfterKeys raw first second) := by
    have hs := vector_swap_remove_two_zero
      (Spec.metadataHeader [(first, firstValue), (second, secondValue)]).keys
      (twoMetadataAfterIndex raw first second) first.val second.val
      (by simp [Spec.metadataHeader])
      (by simpa [Spec.metadataHeader, vectorKey] using hkey0)
      (by simpa [Spec.metadataHeader, vectorKey] using hkey1)
      (by simp [vectorKey, Spec.metadataHeader, initialMap, leBytes])
    simpa [twoMetadataAfterKeys, Spec.metadataHeader, vectorKey] using hs
  have hvalue0 : read (twoMetadataAfterKeys raw first second)
      (vectorKey initialMap.values 0) =
      some (Borsh.encodeMetadata firstValue) := by
    have hread : read (twoMetadataAfterIndex raw first second)
        (vectorKey initialMap.values 0) =
        some (Borsh.encodeMetadata firstValue) := by
      apply read_after_index_reassignment
      · exact vector_key_not_metadata_index initialMap.values 0 first (by decide)
      · exact vector_key_not_metadata_index initialMap.values 0 second (by decide)
      · simpa using layout.value 0 (by simp)
    unfold twoMetadataAfterKeys
    rw [read_write_other _ _ _ _ (by decide)]
    rw [read_remove_other _ _ _ (by decide)]
    exact hread
  have hvalue1 : read (twoMetadataAfterKeys raw first second)
      (vectorKey initialMap.values 1) =
      some (Borsh.encodeMetadata secondValue) := by
    have hread : read (twoMetadataAfterIndex raw first second)
        (vectorKey initialMap.values 1) =
        some (Borsh.encodeMetadata secondValue) := by
      apply read_after_index_reassignment
      · exact vector_key_not_metadata_index initialMap.values 1 first (by decide)
      · exact vector_key_not_metadata_index initialMap.values 1 second (by decide)
      · simpa using layout.value 1 (by simp)
    unfold twoMetadataAfterKeys
    rw [read_write_other _ _ _ _ (by decide)]
    rw [read_remove_other _ _ _ (by decide)]
    exact hread
  have hvalues : (vectorSwapRemove (Spec.metadataHeader
      [(first, firstValue), (second, secondValue)]).values 0).run
        (twoMetadataAfterKeys raw first second) =
      .ok ((Borsh.encodeMetadata firstValue,
        { (Spec.metadataHeader
          [(first, firstValue), (second, secondValue)]).values with length := 1 }),
        twoMetadataAfterValues raw first second secondValue) := by
    have hs := vector_swap_remove_two_zero
      (Spec.metadataHeader [(first, firstValue), (second, secondValue)]).values
      (twoMetadataAfterKeys raw first second)
      (Borsh.encodeMetadata firstValue) (Borsh.encodeMetadata secondValue)
      (by simp [Spec.metadataHeader])
      (by simpa [Spec.metadataHeader, vectorKey] using hvalue0)
      (by simpa [Spec.metadataHeader, vectorKey] using hvalue1)
      (by simp [vectorKey, Spec.metadataHeader, initialMap, leBytes])
    simpa [twoMetadataAfterValues, Spec.metadataHeader, vectorKey] using hs
  have hdecode : Borsh.exact (Borsh.natural 8) (leBytes 8 0) = some 0 := by decide
  have hmetadata := exact_metadata_encode_bounded firstValue hbounded.1 hbounded.2
  simp [Spec.metadataHeader, initialMap, mapIndexKey] at hindex hlastGet hkeys hvalues
  simp only [twoMetadataAfterIndex, twoMetadataAfterKeys, twoMetadataAfterValues] at hkeys hvalues
  simp [initialMap, mapIndexKey, vectorKey] at hkeys hvalues
  simp [mapRemove, Spec.metadataHeader, initialMap, mapIndexKey, vectorKey,
    hindex, hlastGet, hneqval, hdecode, hkeys, hvalues, hmetadata,
    twoMetadataAfterIndex, twoMetadataAfterKeys, twoMetadataAfterValues,
    mapLength, load, save, erase, require, expect, Bind.bind, Pure.pure,
    Tx.run_bind, Tx.bind, Tx.run, Except.bind]

def twoMetadataDeletedRaw (raw : Raw) (first second : Hash)
    (secondValue : Metadata) : Raw :=
  write (twoMetadataAfterValues raw first second secondValue) metadataKey
    (Borsh.encodeMap (Spec.metadataHeader [(second, secondValue)]))

theorem two_metadata_delete_entry (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)])
    (hbounded : Spec.MetadataBounded firstValue)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.deleteMetadata first) =
      .ok ⟨twoMetadataDeletedRaw raw first second secondValue, [], .unit⟩ := by
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
  have hremove := two_metadata_swap_remove raw first second firstValue
    secondValue layout hbounded
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, loadMap, layout.header, hmap, hremove, twoMetadataDeletedRaw,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem two_metadata_delete_preserves_layout (raw : Raw)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)]) :
    Spec.MetadataLayout (twoMetadataDeletedRaw raw first second secondValue)
      [(second, secondValue)] := by
  have hdistinct : first ≠ second := by
    simpa using layout.unique
  have hdistinctVal : first.val ≠ second.val := by
    intro he
    exact hdistinct (Subtype.ext he)
  constructor
  · simp
  · exact read_write_self _ _ _
  · intro query
    have hheader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
    have hvalue0 : mapIndexKey initialMap query ≠ vectorKey initialMap.values 0 := by
      exact (vector_key_not_metadata_index initialMap.values 0 query (by decide)).symm
    have hvalue1 : mapIndexKey initialMap query ≠ vectorKey initialMap.values 1 := by
      exact (vector_key_not_metadata_index initialMap.values 1 query (by decide)).symm
    have hkey0 : mapIndexKey initialMap query ≠ vectorKey initialMap.keys 0 := by
      exact (vector_key_not_metadata_index initialMap.keys 0 query (by decide)).symm
    have hkey1 : mapIndexKey initialMap query ≠ vectorKey initialMap.keys 1 := by
      exact (vector_key_not_metadata_index initialMap.keys 1 query (by decide)).symm
    unfold twoMetadataDeletedRaw twoMetadataAfterValues twoMetadataAfterKeys
    rw [read_write_other _ _ _ _ hheader]
    rw [read_write_other _ _ _ _ hvalue0]
    rw [read_remove_other _ _ _ hvalue1]
    rw [read_write_other _ _ _ _ hkey0]
    rw [read_remove_other _ _ _ hkey1]
    by_cases hsecond : query = second
    · subst query
      unfold twoMetadataAfterIndex
      simp [Spec.findHash, read_write_self]
    · have hnotSecond : mapIndexKey initialMap query ≠
          mapIndexKey initialMap second := by
        intro he
        exact hsecond (canonical_map_index_injective query second he)
      unfold twoMetadataAfterIndex
      rw [read_write_other _ _ _ _ hnotSecond]
      by_cases hfirst : query = first
      · subst query
        have hsecondVal : second.val ≠ first.val := Ne.symm hdistinctVal
        simp [read_remove_self, Spec.findHash, hsecondVal]
      · have hnotFirst : mapIndexKey initialMap query ≠
            mapIndexKey initialMap first := by
          intro he
          exact hfirst (canonical_map_index_injective query first he)
        rw [read_remove_other _ _ _ hnotFirst]
        have hnotFirstVal : first.val ≠ query.val := by
          intro he
          exact hfirst (Subtype.ext he.symm)
        have hnotSecondVal : second.val ≠ query.val := by
          intro he
          exact hsecond (Subtype.ext he.symm)
        simpa [Spec.findHash, hnotFirstVal, hnotSecondVal] using layout.index query
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hheader : vectorKey initialMap.keys 0 ≠ metadataKey := by decide
    have hvalue0 : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.values 0 := by decide
    have hvalue1 : vectorKey initialMap.keys 0 ≠ vectorKey initialMap.values 1 := by decide
    unfold twoMetadataDeletedRaw twoMetadataAfterValues twoMetadataAfterKeys
    rw [read_write_other _ _ _ _ hheader]
    rw [read_write_other _ _ _ _ hvalue0]
    rw [read_remove_other _ _ _ hvalue1]
    simp [read_write_self]
  · intro index hindex
    have hi : index = 0 := by simpa using hindex
    subst index
    have hheader : vectorKey initialMap.values 0 ≠ metadataKey := by decide
    unfold twoMetadataDeletedRaw twoMetadataAfterValues
    rw [read_write_other _ _ _ _ hheader]
    simp [read_write_self]

theorem two_metadata_delete_entry_preserves_layout (cfg : Config)
    (raw : Raw) (env : Env) (setHeader : SetHeader)
    (first second : Hash) (firstValue secondValue : Metadata)
    (layout : Spec.MetadataLayout raw
      [(first, firstValue), (second, secondValue)])
    (hbounded : Spec.MetadataBounded firstValue)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata first) = .ok out) :
    Spec.MetadataLayout out.raw [(second, secondValue)] := by
  rw [two_metadata_delete_entry cfg raw env setHeader first second firstValue
    secondValue layout hbounded hstate hsetIndex hsetLength hsetPrefix howner]
    at hstep
  cases hstep
  exact two_metadata_delete_preserves_layout raw first second firstValue
    secondValue layout

theorem two_metadata_delete_preserves_state (raw : Raw)
    (first second : Hash) (secondValue : Metadata) :
    read (twoMetadataDeletedRaw raw first second secondValue) stateKey =
      read raw stateKey := by
  have hindexFirst : stateKey ≠ mapIndexKey initialMap first := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, first.property] at hlen
  have hindexSecond : stateKey ≠ mapIndexKey initialMap second := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, second.property] at hlen
  unfold twoMetadataDeletedRaw twoMetadataAfterValues twoMetadataAfterKeys
    twoMetadataAfterIndex
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ metadataKey)]
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ vectorKey initialMap.values 0)]
  rw [read_remove_other _ _ _ (by decide : stateKey ≠ vectorKey initialMap.values 1)]
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ vectorKey initialMap.keys 0)]
  rw [read_remove_other _ _ _ (by decide : stateKey ≠ vectorKey initialMap.keys 1)]
  rw [read_write_other _ _ _ _ hindexSecond]
  rw [read_remove_other _ _ _ hindexFirst]

theorem two_metadata_delete_then_get (cfg : Config) (raw : Raw)
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
    (hstep : step cfg raw env (.deleteMetadata first) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata [(second, secondValue)]⟩ := by
  rw [two_metadata_delete_entry cfg raw env setHeader first second firstValue
    secondValue layout hboundedFirst hstate hsetIndex hsetLength hsetPrefix howner]
    at hstep
  cases hstep
  have hstate' : read (twoMetadataDeletedRaw raw first second secondValue)
      stateKey = some (Borsh.encodeSet setHeader) := by
    rw [two_metadata_delete_preserves_state]
    exact hstate
  apply metadata_getter_matches_layout cfg _ env setHeader
    [(second, secondValue)] hstate' hsetIndex hsetLength hsetPrefix
  · exact two_metadata_delete_preserves_layout raw first second firstValue
      secondValue layout
  · simp
  · intro entry hentry
    simp at hentry
    subst entry
    exact hboundedSecond

end SputnikFactory
