import Proofs.MetadataAbsentDelete

namespace SputnikFactory

def replaceMetadataAt (order : List (Hash × Metadata))
    (index : Nat) (hash : Hash) (replacement : Metadata) :
    List (Hash × Metadata) :=
  order.set index (hash, replacement)

theorem replace_metadata_keys (order : List (Hash × Metadata))
    (index : Nat) (hash : Hash) (previous replacement : Metadata)
    (hentry : order[index]? = some (hash, previous)) :
    (replaceMetadataAt order index hash replacement).map Prod.fst =
      order.map Prod.fst := by
  induction order generalizing index with
  | nil =>
    cases index <;> simp at hentry
  | cons head tail ih =>
    cases index with
    | zero =>
      simp at hentry
      subst head
      simp [replaceMetadataAt]
    | succ index =>
      simp at hentry
      simpa [replaceMetadataAt] using ih index hentry

theorem find_hash_replace_metadata (order : List (Hash × Metadata))
    (index : Nat) (hash query : Hash) (previous replacement : Metadata)
    (hentry : order[index]? = some (hash, previous)) :
    Spec.findHash (replaceMetadataAt order index hash replacement) query =
      Spec.findHash order query := by
  induction order generalizing index with
  | nil =>
    cases index <;> simp at hentry
  | cons head tail ih =>
    cases index with
    | zero =>
      simp at hentry
      subst head
      simp [replaceMetadataAt, Spec.findHash]
    | succ index =>
      simp at hentry
      change (if head.1 == query then some 0 else
        (Spec.findHash (replaceMetadataAt tail index hash replacement) query).map Nat.succ) =
        (if head.1 == query then some 0 else
          (Spec.findHash tail query).map Nat.succ)
      rw [ih index hentry]

theorem vector_value_key_injective_bounded (left right : Nat)
    (hleft : left < 256 ^ 8) (hright : right < 256 ^ 8)
    (heq : vectorKey initialMap.values left =
      vectorKey initialMap.values right) :
    left = right := by
  have hbytes : leBytes 8 left = leBytes 8 right := by
    simpa [vectorKey] using List.append_cancel_left heq
  have hdecode := congrArg Borsh.fromLE hbytes
  simpa [fromLE_leBytes, hleft, hright] using hdecode

def metadataReplacementRaw (raw : Raw) (order : List (Hash × Metadata))
    (index : Nat) (replacement : Metadata) : Raw :=
  write
    (write raw (vectorKey initialMap.values index)
      (Borsh.encodeMetadata replacement))
    metadataKey (Borsh.encodeMap (Spec.metadataHeader order))

theorem metadata_replacement_preserves_layout (raw : Raw)
    (order : List (Hash × Metadata)) (index : Nat)
    (hash : Hash) (previous replacement : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hentry : order[index]? = some (hash, previous))
    (horderLength : order.length < 256 ^ 8) :
    Spec.MetadataLayout (metadataReplacementRaw raw order index replacement)
      (replaceMetadataAt order index hash replacement) := by
  have hindex : index < order.length := (List.getElem?_eq_some_iff.mp hentry).1
  have hkeys := replace_metadata_keys order index hash previous replacement hentry
  have hheader : Spec.metadataHeader
      (replaceMetadataAt order index hash replacement) =
      Spec.metadataHeader order := by
    simp [Spec.metadataHeader, replaceMetadataAt]
  constructor
  · simpa [hkeys] using layout.unique
  · rw [hheader]
    exact read_write_self _ _ _
  · intro query
    have hnotHeader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
    have hnotValue : mapIndexKey initialMap query ≠
        vectorKey initialMap.values index := by
      exact (vector_key_not_metadata_index initialMap.values index query
        (by decide)).symm
    unfold metadataReplacementRaw
    rw [read_write_other _ _ _ _ hnotHeader]
    rw [read_write_other _ _ _ _ hnotValue]
    rw [find_hash_replace_metadata order index hash query previous replacement hentry]
    exact layout.index query
  · intro i hi
    have hi' : i < order.length := by simpa [replaceMetadataAt] using hi
    have hnotHeader : vectorKey initialMap.keys i ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlen
    have hnotValue : vectorKey initialMap.keys i ≠
        vectorKey initialMap.values index := by
      simp [vectorKey, initialMap]
    unfold metadataReplacementRaw
    rw [read_write_other _ _ _ _ hnotHeader]
    rw [read_write_other _ _ _ _ hnotValue]
    by_cases he : i = index
    · subst i
      have hpost : (replaceMetadataAt order index hash replacement)[index]? =
          some (hash, replacement) := by
        simp [replaceMetadataAt, List.getElem?_set_self hindex]
      rw [hpost]
      simpa [hentry] using layout.key index hindex
    · have hpost : (replaceMetadataAt order index hash replacement)[i]? =
          order[i]? := by
        simpa [replaceMetadataAt] using
          (List.getElem?_set_ne (Ne.symm he) :
            (order.set index (hash, replacement))[i]? = order[i]?)
      rw [hpost]
      exact layout.key i hi'
  · intro i hi
    have hi' : i < order.length := by simpa [replaceMetadataAt] using hi
    have hnotHeader : vectorKey initialMap.values i ≠ metadataKey := by
      intro he
      have hlen := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlen
    unfold metadataReplacementRaw
    rw [read_write_other _ _ _ _ hnotHeader]
    by_cases he : i = index
    · subst i
      have hpost : (replaceMetadataAt order index hash replacement)[index]? =
          some (hash, replacement) := by
        simp [replaceMetadataAt, List.getElem?_set_self hindex]
      rw [hpost]
      simp [read_write_self]
    · have hdistinct : vectorKey initialMap.values i ≠
          vectorKey initialMap.values index := by
        intro heq
        have hiBound : i < 256 ^ 8 := Nat.lt_trans hi' horderLength
        have hindexBound : index < 256 ^ 8 := Nat.lt_trans hindex horderLength
        exact he (vector_value_key_injective_bounded i index hiBound
          hindexBound heq)
      rw [read_write_other _ _ _ _ hdistinct]
      have hpost : (replaceMetadataAt order index hash replacement)[i]? =
          order[i]? := by
        simpa [replaceMetadataAt] using
          (List.getElem?_set_ne (Ne.symm he) :
            (order.set index (hash, replacement))[i]? = order[i]?)
      rw [hpost]
      exact layout.value i hi'

theorem store_metadata_replacement_preserves_layout_general
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (index : Nat)
    (previous replacement : Metadata) (code : Bytes)
    (layout : Spec.MetadataLayout raw order)
    (hentry : order[index]? = some (hash, previous))
    (horderLength : order.length < 256 ^ 8)
    (hboundedPrevious : Spec.MetadataBounded previous)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hindex : read raw (mapIndexKey initialMap hash) =
      some (leBytes 8 index))
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash replacement false) = .ok out) :
    Spec.MetadataLayout out.raw
      (replaceMetadataAt order index hash replacement) := by
  have hbound : index < order.length := (List.getElem?_eq_some_iff.mp hentry).1
  have hvalue : read raw (vectorKey initialMap.values index) =
      some (Borsh.encodeMetadata previous) := by
    simpa [hentry] using layout.value index hbound
  rw [store_metadata_valid_replacement_general cfg raw env setHeader order
    hash index previous replacement code hstate hsetIndex hsetLength
    hsetPrefix howner hcode layout.header horderLength hindex hbound
    hvalue hboundedPrevious] at hstep
  cases hstep
  exact metadata_replacement_preserves_layout raw order index hash previous
    replacement layout hentry horderLength

theorem bounded_replace_metadata (order : List (Hash × Metadata))
    (index : Nat) (hash : Hash) (replacement : Metadata)
    (hbounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (hreplacement : Spec.MetadataBounded replacement) :
    ∀ entry ∈ replaceMetadataAt order index hash replacement,
      Spec.MetadataBounded entry.2 := by
  intro entry hmem
  rcases List.mem_or_eq_of_mem_set (by simpa [replaceMetadataAt] using hmem) with
    hprevious | hnew
  · exact hbounded entry hprevious
  · subst entry
    exact hreplacement

theorem metadata_replacement_preserves_state (raw : Raw)
    (order : List (Hash × Metadata)) (index : Nat)
    (replacement : Metadata) :
    read (metadataReplacementRaw raw order index replacement) stateKey =
      read raw stateKey := by
  have hvalue : stateKey ≠ vectorKey initialMap.values index := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  unfold metadataReplacementRaw
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ metadataKey)]
  rw [read_write_other _ _ _ _ hvalue]

theorem store_metadata_replacement_then_get_general
    (cfg : Config) (raw : Raw) (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (index : Nat)
    (previous replacement : Metadata) (code : Bytes)
    (layout : Spec.MetadataLayout raw order)
    (hentry : order[index]? = some (hash, previous))
    (horderLength : order.length < 256 ^ 8)
    (hbounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (hreplacement : Spec.MetadataBounded replacement)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (hcode : read raw hash.val = some code)
    (hindex : read raw (mapIndexKey initialMap hash) =
      some (leBytes 8 index))
    (out : Outcome)
    (hstep : step cfg raw env (.storeMetadata hash replacement false) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata
        (replaceMetadataAt order index hash replacement)⟩ := by
  have hbound : index < order.length := (List.getElem?_eq_some_iff.mp hentry).1
  have hvalue : read raw (vectorKey initialMap.values index) =
      some (Borsh.encodeMetadata previous) := by
    simpa [hentry] using layout.value index hbound
  have hprev := hbounded (hash, previous) (List.mem_of_getElem? hentry)
  rw [store_metadata_valid_replacement_general cfg raw env setHeader order
    hash index previous replacement code hstate hsetIndex hsetLength
    hsetPrefix howner hcode layout.header horderLength hindex hbound
    hvalue hprev] at hstep
  cases hstep
  have hstate' : read (metadataReplacementRaw raw order index replacement)
      stateKey = some (Borsh.encodeSet setHeader) := by
    rw [metadata_replacement_preserves_state]
    exact hstate
  have hpostLength : (replaceMetadataAt order index hash replacement).length <
      256 ^ 8 := by
    simpa [replaceMetadataAt] using horderLength
  exact metadata_getter_matches_layout cfg _ env setHeader
    (replaceMetadataAt order index hash replacement) hstate'
    hsetIndex hsetLength hsetPrefix
    (metadata_replacement_preserves_layout raw order index hash previous
      replacement layout hentry horderLength)
    hpostLength
    (bounded_replace_metadata order index hash replacement hbounded hreplacement)

end SputnikFactory
