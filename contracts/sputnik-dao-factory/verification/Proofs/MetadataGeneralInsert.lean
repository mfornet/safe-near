import Proofs.MetadataGeneralLayout

namespace SputnikFactory

def metadataAppendBodyRaw (raw : Raw) (order : List (Hash × Metadata))
    (hash : Hash) (value : Metadata) : Raw :=
  write
    (write
      (write raw (mapIndexKey initialMap hash) (leBytes 8 order.length))
      (vectorKey initialMap.keys order.length) hash.val)
    (vectorKey initialMap.values order.length) (Borsh.encodeMetadata value)

def metadataAppendRaw (raw : Raw) (order : List (Hash × Metadata))
    (hash : Hash) (value : Metadata) : Raw :=
  write (metadataAppendBodyRaw raw order hash value) metadataKey
    (Borsh.encodeMap (Spec.metadataHeader (order ++ [(hash, value)])))

/-- The absent-key path appends the index and both vectors at the old length.
The strict room condition reflects `Vector::push_raw`'s post-write u64 guard. -/
theorem map_insert_absent_general (header : MapHeader) (raw : Raw)
    (hash : Hash) (value : Metadata)
    (habsent : read raw (mapIndexKey header hash) = none)
    (hequal : header.keys.length = header.values.length)
    (hroom : header.keys.length + 1 < u64Bound) :
    (mapInsert header hash value).run raw =
      .ok ({ header with
        keys := { header.keys with length := header.keys.length + 1 },
        values := { header.values with length := header.values.length + 1 } },
        write
          (write
            (write raw (mapIndexKey header hash)
              (leBytes 8 header.keys.length))
            (vectorKey header.keys header.keys.length) hash.val)
          (vectorKey header.values header.values.length)
          (Borsh.encodeMetadata value)) := by
  have hroomValues : header.values.length + 1 < u64Bound := by
    simpa [hequal] using hroom
  simp [mapInsert, habsent, mapLength, hequal, vectorPush,
    hroomValues, load, save, require, Bind.bind, Pure.pure,
    Tx.bind, Tx.run]

theorem canonical_map_insert_absent_general (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hroom : order.length + 1 < u64Bound) :
    (mapInsert (Spec.metadataHeader order) hash value).run raw =
      .ok (Spec.metadataHeader (order ++ [(hash, value)]),
        metadataAppendBodyRaw raw order hash value) := by
  have habsent' : read raw (mapIndexKey (Spec.metadataHeader order) hash) =
      none := by
    simpa [Spec.metadataHeader, mapIndexKey] using habsent
  have hrun := map_insert_absent_general (Spec.metadataHeader order) raw hash value
    habsent' (by rfl) (by simpa [Spec.metadataHeader] using hroom)
  simpa [metadataAppendBodyRaw, Spec.metadataHeader, initialMap,
    mapIndexKey, vectorKey] using hrun

theorem find_hash_append_other (order : List (Hash × Metadata))
    (hash query : Hash) (value : Metadata) (hne : hash ≠ query) :
    Spec.findHash (order ++ [(hash, value)]) query =
      Spec.findHash order query := by
  induction order with
  | nil =>
    have hval : hash.val ≠ query.val := by
      intro he
      exact hne (Subtype.ext he)
    simp [Spec.findHash, hval]
  | cons head tail ih =>
    simp only [List.cons_append, Spec.findHash]
    rw [ih]

theorem find_hash_append_new (order : List (Hash × Metadata))
    (hash : Hash) (value : Metadata)
    (habsent : Spec.findHash order hash = none) :
    Spec.findHash (order ++ [(hash, value)]) hash = some order.length := by
  induction order with
  | nil =>
    simp [Spec.findHash]
  | cons head tail ih =>
    have hhead : head.1.val ≠ hash.val := by
      intro he
      simp [Spec.findHash, he] at habsent
    have htail : Spec.findHash tail hash = none := by
      simpa [Spec.findHash, hhead] using habsent
    simp [Spec.findHash, hhead, ih htail]

theorem find_hash_none_not_mem (order : List (Hash × Metadata))
    (hash : Hash) (habsent : Spec.findHash order hash = none) :
    hash ∉ order.map Prod.fst := by
  induction order with
  | nil => simp
  | cons head tail ih =>
    have hhead : head.1 ≠ hash := by
      intro he
      subst hash
      simp [Spec.findHash] at habsent
    have htail : Spec.findHash tail hash = none := by
      have hheadVal : head.1.val ≠ hash.val := by
        intro he
        exact hhead (Subtype.ext he)
      simpa [Spec.findHash, hheadVal] using habsent
    have hne : hash ≠ head.1 := Ne.symm hhead
    simp [hne, ih htail]

theorem find_hash_not_mem_none (order : List (Hash × Metadata))
    (hash : Hash) (hnotmem : hash ∉ order.map Prod.fst) :
    Spec.findHash order hash = none := by
  induction order with
  | nil => rfl
  | cons head tail ih =>
    have hne : head.1 ≠ hash := by
      intro he
      exact hnotmem (by simp [he])
    have htail : hash ∉ tail.map Prod.fst := by
      intro hmem
      exact hnotmem (by simp [hmem])
    have hneVal : head.1.val ≠ hash.val := by
      intro he
      exact hne (Subtype.ext he)
    simp [Spec.findHash, hneVal, ih htail]

theorem vector_key_injective_bounded (header : VectorHeader)
    (left right : Nat) (hleft : left < 256 ^ 8)
    (hright : right < 256 ^ 8)
    (heq : vectorKey header left = vectorKey header right) :
    left = right := by
  have hbytes : leBytes 8 left = leBytes 8 right := by
    simpa [vectorKey] using List.append_cancel_left heq
  have hdecode := congrArg Borsh.fromLE hbytes
  simpa [fromLE_leBytes, hleft, hright] using hdecode

theorem metadata_append_preserves_layout (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (habsent : Spec.findHash order hash = none)
    (hroom : order.length + 1 < u64Bound) :
    Spec.MetadataLayout (metadataAppendRaw raw order hash value)
      (order ++ [(hash, value)]) := by
  have hnotmem := find_hash_none_not_mem order hash habsent
  have horderBound : order.length < 256 ^ 8 := by
    simp [u64Bound] at hroom
    omega
  constructor
  · simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    constructor
    · exact layout.unique
    constructor
    · simp
    · intro key hkey other hother
      simp at hother
      subst other
      intro he
      exact hnotmem (he ▸ hkey)
  · exact read_write_self _ _ _
  · intro query
    have hheader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
    have hvalue : mapIndexKey initialMap query ≠
        vectorKey initialMap.values order.length := by
      exact (vector_key_not_metadata_index initialMap.values order.length query
        (by decide)).symm
    have hkey : mapIndexKey initialMap query ≠
        vectorKey initialMap.keys order.length := by
      exact (vector_key_not_metadata_index initialMap.keys order.length query
        (by decide)).symm
    unfold metadataAppendRaw metadataAppendBodyRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_write_other _ _ _ _ hvalue]
    rw [read_write_other _ _ _ _ hkey]
    by_cases hq : query = hash
    · subst query
      rw [read_write_self]
      simp [find_hash_append_new order hash value habsent]
    · have hnotIndex : mapIndexKey initialMap query ≠
          mapIndexKey initialMap hash := by
        intro he
        exact hq (canonical_map_index_injective query hash he)
      rw [read_write_other _ _ _ _ hnotIndex]
      rw [find_hash_append_other order hash query value (Ne.symm hq)]
      exact layout.index query
  · intro i hi
    have hi' : i < order.length + 1 := by simpa using hi
    have hheader : vectorKey initialMap.keys i ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlen
    have hvalue : vectorKey initialMap.keys i ≠
        vectorKey initialMap.values order.length := by
      simp [vectorKey, initialMap]
    unfold metadataAppendRaw metadataAppendBodyRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_write_other _ _ _ _ hvalue]
    by_cases he : i = order.length
    · subst i
      rw [read_write_self]
      simp
    · have hiOld : i < order.length := by omega
      have hnotKey : vectorKey initialMap.keys i ≠
          vectorKey initialMap.keys order.length := by
        intro heq
        have hiBound : i < 256 ^ 8 := Nat.lt_trans hiOld horderBound
        exact he (vector_key_injective_bounded initialMap.keys i
          order.length hiBound horderBound heq)
      have hnotIndex : vectorKey initialMap.keys i ≠
          mapIndexKey initialMap hash :=
        vector_key_not_metadata_index initialMap.keys i hash (by decide)
      rw [read_write_other _ _ _ _ hnotKey]
      rw [read_write_other _ _ _ _ hnotIndex]
      rw [List.getElem?_append_left hiOld]
      exact layout.key i hiOld
  · intro i hi
    have hi' : i < order.length + 1 := by simpa using hi
    have hheader : vectorKey initialMap.values i ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlen
    unfold metadataAppendRaw metadataAppendBodyRaw
    rw [read_write_other _ _ _ _ hheader]
    by_cases he : i = order.length
    · subst i
      rw [read_write_self]
      simp
    · have hiOld : i < order.length := by omega
      have hnotValue : vectorKey initialMap.values i ≠
          vectorKey initialMap.values order.length := by
        intro heq
        have hiBound : i < 256 ^ 8 := Nat.lt_trans hiOld horderBound
        exact he (vector_key_injective_bounded initialMap.values i
          order.length hiBound horderBound heq)
      have hnotKey : vectorKey initialMap.values i ≠
          vectorKey initialMap.keys order.length := by
        simp [vectorKey, initialMap]
      have hnotIndex : vectorKey initialMap.values i ≠
          mapIndexKey initialMap hash :=
        vector_key_not_metadata_index initialMap.values i hash (by decide)
      rw [read_write_other _ _ _ _ hnotValue]
      rw [read_write_other _ _ _ _ hnotKey]
      rw [read_write_other _ _ _ _ hnotIndex]
      rw [List.getElem?_append_left hiOld]
      exact layout.value i hiOld

theorem metadata_absent_index_is_not_in_order (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash)
    (layout : Spec.MetadataLayout raw order)
    (habsent : read raw (mapIndexKey initialMap hash) = none) :
    Spec.findHash order hash = none := by
  have h := layout.index hash
  rw [habsent] at h
  cases hfind : Spec.findHash order hash with
  | none => rfl
  | some index => simp [hfind] at h

theorem store_metadata_append_entry (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (code : Bytes)
    (layout : Spec.MetadataLayout raw order)
    (hroom : order.length + 1 < u64Bound)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code) :
    step cfg raw env (.storeMetadata hash value false) =
      .ok ⟨metadataAppendRaw raw order hash value, [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have horderLength : order.length < 256 ^ 8 := by
    simp [u64Bound] at hroom
    omega
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader order)) =
      some (Spec.metadataHeader order) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderLength
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderLength
    · simp [Spec.metadataHeader, initialMap]
  have hinsert := canonical_map_insert_absent_general raw order hash value
    habsent hroom
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, hcode, layout.header, hmap, hinsert, metadataAppendRaw,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem store_metadata_append_preserves_layout (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (code : Bytes) (layout : Spec.MetadataLayout raw order)
    (hroom : order.length + 1 < u64Bound)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash value false) = .ok out) :
    Spec.MetadataLayout out.raw (order ++ [(hash, value)]) := by
  rw [store_metadata_append_entry cfg raw env setHeader order hash value code
    layout hroom habsent hstate hsetIndex hsetLength hsetPrefix howner hcode]
    at hstep
  cases hstep
  exact metadata_append_preserves_layout raw order hash value layout
    (metadata_absent_index_is_not_in_order raw order hash layout habsent) hroom

theorem metadata_append_preserves_state (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata) :
    read (metadataAppendRaw raw order hash value) stateKey =
      read raw stateKey := by
  have hindex : stateKey ≠ mapIndexKey initialMap hash := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, hash.property] at hlen
  have hvalue : stateKey ≠ vectorKey initialMap.values order.length := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  have hkey : stateKey ≠ vectorKey initialMap.keys order.length := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  unfold metadataAppendRaw metadataAppendBodyRaw
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ metadataKey)]
  rw [read_write_other _ _ _ _ hvalue]
  rw [read_write_other _ _ _ _ hkey]
  rw [read_write_other _ _ _ _ hindex]

theorem store_metadata_append_then_get (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (code : Bytes) (layout : Spec.MetadataLayout raw order)
    (hroom : order.length + 1 < u64Bound)
    (hbounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (hvalueBounded : Spec.MetadataBounded value)
    (habsent : read raw (mapIndexKey initialMap hash) = none)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash value false) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata (order ++ [(hash, value)])⟩ := by
  rw [store_metadata_append_entry cfg raw env setHeader order hash value code
    layout hroom habsent hstate hsetIndex hsetLength hsetPrefix howner hcode]
    at hstep
  cases hstep
  have hstate' : read (metadataAppendRaw raw order hash value) stateKey =
      some (Borsh.encodeSet setHeader) := by
    rw [metadata_append_preserves_state]
    exact hstate
  have hpostLength : (order ++ [(hash, value)]).length < 256 ^ 8 := by
    simpa [u64Bound] using hroom
  have hpostBounded : ∀ entry ∈ order ++ [(hash, value)],
      Spec.MetadataBounded entry.2 := by
    intro entry hentry
    rcases List.mem_append.mp hentry with hbefore | hnew
    · exact hbounded entry hbefore
    · simp at hnew
      subst entry
      exact hvalueBounded
  exact metadata_getter_matches_layout cfg _ env setHeader
    (order ++ [(hash, value)]) hstate' hsetIndex hsetLength hsetPrefix
    (metadata_append_preserves_layout raw order hash value layout
      (metadata_absent_index_is_not_in_order raw order hash layout habsent) hroom)
    hpostLength hpostBounded

end SputnikFactory
