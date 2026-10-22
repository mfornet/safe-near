import Proofs.MetadataGeneralInsert

namespace SputnikFactory

/-- Nonempty vector pop removes exactly its final record. -/
theorem vector_pop_present (header : VectorHeader) (raw : Raw)
    (last : Bytes) (hpositive : 0 < header.length)
    (hlast : read raw (vectorKey header (header.length - 1)) = some last) :
    (vectorPop header).run raw =
      .ok (some (last, { header with length := header.length - 1 }),
        remove raw (vectorKey header (header.length - 1))) := by
  have hne : header.length ≠ 0 := Nat.ne_of_gt hpositive
  simp [vectorPop, hne, hlast, load, erase, expect,
    Bind.bind, Pure.pure, Tx.bind, Tx.run]

/-- The final-slot branch of swap removal is exactly a vector pop. -/
theorem vector_swap_remove_last (header : VectorHeader) (raw : Raw)
    (index : Nat) (last : Bytes)
    (hfinal : index + 1 = header.length)
    (hlast : read raw (vectorKey header index) = some last) :
    (vectorSwapRemove header index).run raw =
      .ok ((last, { header with length := index }),
        remove raw (vectorKey header index)) := by
  have hpositive : 0 < header.length := by omega
  have hindex : index < header.length := by omega
  have hidxeq : header.length - 1 = index := by omega
  have hlast' : read raw (vectorKey header (header.length - 1)) =
      some last := by simpa [hidxeq] using hlast
  have hpop := vector_pop_present header raw last hpositive hlast'
  simp [vectorSwapRemove, hindex, hfinal, hpop, require, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]
  simp [hidxeq]

/-- A nonfinal removal first pops the final slot and then replaces the target
slot with that value. -/
theorem vector_swap_remove_middle (header : VectorHeader) (raw : Raw)
    (index : Nat) (previous last : Bytes)
    (hmiddle : index + 1 < header.length)
    (hread : read raw (vectorKey header index) = some previous)
    (hlast : read raw (vectorKey header (header.length - 1)) = some last)
    (hdistinct : vectorKey header index ≠
      vectorKey header (header.length - 1)) :
    (vectorSwapRemove header index).run raw =
      .ok ((previous, { header with length := header.length - 1 }),
        write (remove raw (vectorKey header (header.length - 1)))
          (vectorKey header index) last) := by
  have hpositive : 0 < header.length := by omega
  have hindex : index < header.length := by omega
  have hnotFinal : index + 1 ≠ header.length := by omega
  have hpop := vector_pop_present header raw last hpositive hlast
  have hread' : read (remove raw (vectorKey header (header.length - 1)))
      (vectorKey header index) = some previous := by
    rw [read_remove_other _ _ _ hdistinct]
    exact hread
  have hreplace := vector_replace_present
    { header with length := header.length - 1 }
    (remove raw (vectorKey header (header.length - 1)))
    index previous last (by change index < header.length - 1; omega)
    (by simpa [vectorKey] using hread')
  simp [vectorSwapRemove, hindex, hnotFinal, hpop, hreplace, require, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]
  simp [vectorKey]

def metadataTailRemovedRaw (raw : Raw) (hash : Hash) (count : Nat) : Raw :=
  remove
    (remove
      (remove raw (mapIndexKey initialMap hash))
      (vectorKey initialMap.keys (count - 1)))
    (vectorKey initialMap.values (count - 1))

def metadataReducedHeader (order : List (Hash × Metadata)) : MapHeader :=
  { Spec.metadataHeader order with
    keys := { (Spec.metadataHeader order).keys with length := order.length - 1 },
    values := { (Spec.metadataHeader order).values with length := order.length - 1 } }

/-- The nonfinal branch first removes the deleted hash's index and points the
last hash at the vacated position. Both vector swaps happen afterward. -/
def metadataMiddleIndexRaw (raw : Raw) (removed moved : Hash)
    (index : Nat) : Raw :=
  write (remove raw (mapIndexKey initialMap removed))
    (mapIndexKey initialMap moved) (leBytes 8 index)

def metadataMiddleKeysRaw (raw : Raw) (removed moved : Hash)
    (index count : Nat) : Raw :=
  write
    (remove (metadataMiddleIndexRaw raw removed moved index)
      (vectorKey initialMap.keys (count - 1)))
    (vectorKey initialMap.keys index) moved.val

def metadataMiddleValuesRaw (raw : Raw) (removed moved : Hash)
    (index count : Nat) (movedValue : Metadata) : Raw :=
  write
    (remove (metadataMiddleKeysRaw raw removed moved index count)
      (vectorKey initialMap.values (count - 1)))
    (vectorKey initialMap.values index) (Borsh.encodeMetadata movedValue)

theorem metadata_order_split_last (order : List (Hash × Metadata))
    (hash : Hash) (value : Metadata)
    (hlast : order[order.length - 1]? = some (hash, value)) :
    order = order.take (order.length - 1) ++ [(hash, value)] := by
  have hgetLast : order.getLast? = some (hash, value) := by
    simpa [List.getLast?_eq_getElem?] using hlast
  have hsplit := List.take_append_getLast? order
  rw [hgetLast] at hsplit
  simpa using hsplit.symm

theorem metadata_reduced_header_eq_take (order : List (Hash × Metadata)) :
    metadataReducedHeader order =
      Spec.metadataHeader (order.take (order.length - 1)) := by
  have hlen : (order.take (order.length - 1)).length = order.length - 1 := by
    simp [Nat.sub_le]
  simp [metadataReducedHeader, Spec.metadataHeader, hlen]

/-- Exact raw effect of removing a nonfinal metadata entry. The read premises
make the storage-consistency requirements explicit: both target slots and both
last slots must exist, and the evicted value must decode successfully. -/
theorem map_remove_middle_general (raw : Raw)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index : Nat) (oldValue movedValue : Metadata)
    (hmiddle : index + 1 < order.length)
    (horderBound : order.length < 256 ^ 8)
    (hdifferent : moved.val ≠ removed.val)
    (hindex : read raw (mapIndexKey initialMap removed) = some (leBytes 8 index))
    (hlast : read raw (vectorKey initialMap.keys (order.length - 1)) =
      some moved.val)
    (hkey : read (metadataMiddleIndexRaw raw removed moved index)
      (vectorKey initialMap.keys index) = some removed.val)
    (hlastKey : read (metadataMiddleIndexRaw raw removed moved index)
      (vectorKey initialMap.keys (order.length - 1)) = some moved.val)
    (hvalue : read (metadataMiddleKeysRaw raw removed moved index order.length)
      (vectorKey initialMap.values index) = some (Borsh.encodeMetadata oldValue))
    (hlastValue : read (metadataMiddleKeysRaw raw removed moved index order.length)
      (vectorKey initialMap.values (order.length - 1)) =
        some (Borsh.encodeMetadata movedValue))
    (hbounded : Spec.MetadataBounded oldValue) :
    (mapRemove (Spec.metadataHeader order) removed).run raw =
      .ok (metadataReducedHeader order,
        metadataMiddleValuesRaw raw removed moved index order.length movedValue) := by
  have hlastGet : (vectorGet (Spec.metadataHeader order).keys
      (order.length - 1)).run raw = .ok (some moved.val, raw) := by
    apply vector_get_present
    · simp [Spec.metadataHeader]; omega
    · simpa [Spec.metadataHeader, vectorKey] using hlast
  have hkeyDistinct : vectorKey (Spec.metadataHeader order).keys index ≠
      vectorKey (Spec.metadataHeader order).keys (order.length - 1) := by
    intro he
    have hi : index < 256 ^ 8 := by omega
    have hj : order.length - 1 < 256 ^ 8 := by omega
    have heq := vector_key_injective_bounded
      (Spec.metadataHeader order).keys index (order.length - 1) hi hj he
    omega
  have hvalueDistinct : vectorKey (Spec.metadataHeader order).values index ≠
      vectorKey (Spec.metadataHeader order).values (order.length - 1) := by
    intro he
    have hi : index < 256 ^ 8 := by omega
    have hj : order.length - 1 < 256 ^ 8 := by omega
    have heq := vector_key_injective_bounded
      (Spec.metadataHeader order).values index (order.length - 1) hi hj he
    omega
  have hkeys := vector_swap_remove_middle
    (Spec.metadataHeader order).keys
    (metadataMiddleIndexRaw raw removed moved index)
    index removed.val moved.val (by simpa [Spec.metadataHeader] using hmiddle)
    (by simpa [Spec.metadataHeader, vectorKey] using hkey)
    (by simpa [Spec.metadataHeader, vectorKey] using hlastKey)
    hkeyDistinct
  have hvalues := vector_swap_remove_middle
    (Spec.metadataHeader order).values
    (metadataMiddleKeysRaw raw removed moved index order.length)
    index (Borsh.encodeMetadata oldValue) (Borsh.encodeMetadata movedValue)
    (by simpa [Spec.metadataHeader] using hmiddle)
    (by simpa [Spec.metadataHeader, vectorKey] using hvalue)
    (by simpa [Spec.metadataHeader, vectorKey] using hlastValue)
    hvalueDistinct
  have hdecode := exact_natural_encode 8 index
    (show index < 256 ^ 8 by omega)
  have hmetadata := exact_metadata_encode_bounded oldValue hbounded.1 hbounded.2
  have hnotOne : order.length ≠ 1 := by omega
  have hpositive : 0 < order.length := by omega
  simp [Spec.metadataHeader, initialMap, mapIndexKey, vectorKey] at hindex hlastGet hkeys hvalues
  simp only [metadataMiddleIndexRaw, metadataMiddleKeysRaw] at hkeys hvalues
  simp [initialMap, mapIndexKey, vectorKey] at hkeys hvalues
  simp [mapRemove, Spec.metadataHeader, initialMap, mapIndexKey, vectorKey,
    hindex, hlastGet, hdifferent, hdecode, hkeys, hvalues, hmetadata,
    metadataReducedHeader, metadataMiddleIndexRaw, metadataMiddleKeysRaw,
    metadataMiddleValuesRaw, mapLength, load, save, erase, require, expect,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind,
    hnotOne, hpositive]

theorem metadata_middle_index_preserves_vector (raw : Raw)
    (removed moved : Hash) (index slot : Nat) (header : VectorHeader)
    (hprefix : header.keyPrefix.length = 2) (value : Bytes)
    (hread : read raw (vectorKey header slot) = some value) :
    read (metadataMiddleIndexRaw raw removed moved index)
      (vectorKey header slot) = some value := by
  unfold metadataMiddleIndexRaw
  rw [read_write_other _ _ _ _
    (vector_key_not_metadata_index header slot moved hprefix)]
  rw [read_remove_other _ _ _
    (vector_key_not_metadata_index header slot removed hprefix)]
  exact hread

theorem metadata_middle_keys_preserves_value (raw : Raw)
    (removed moved : Hash) (index count slot : Nat) (value : Bytes)
    (hread : read raw (vectorKey initialMap.values slot) = some value) :
    read (metadataMiddleKeysRaw raw removed moved index count)
      (vectorKey initialMap.values slot) = some value := by
  unfold metadataMiddleKeysRaw
  rw [read_write_other _ _ _ _ (by simp [vectorKey, initialMap])]
  rw [read_remove_other _ _ _ (by simp [vectorKey, initialMap])]
  exact metadata_middle_index_preserves_vector raw removed moved index slot
    initialMap.values (by decide) value hread

theorem map_remove_middle_from_layout (raw : Raw)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index : Nat) (oldValue movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (horderBound : order.length < 256 ^ 8)
    (hdifferent : moved.val ≠ removed.val)
    (hindex : read raw (mapIndexKey initialMap removed) = some (leBytes 8 index))
    (htarget : order[index]? = some (removed, oldValue))
    (hlast : order[order.length - 1]? = some (moved, movedValue))
    (hbounded : Spec.MetadataBounded oldValue) :
    (mapRemove (Spec.metadataHeader order) removed).run raw =
      .ok (metadataReducedHeader order,
        metadataMiddleValuesRaw raw removed moved index order.length movedValue) := by
  have htargetBound : index < order.length := by omega
  have hlastBound : order.length - 1 < order.length := by omega
  have hlastKey : read raw (vectorKey initialMap.keys (order.length - 1)) =
      some moved.val := by
    simpa [hlast] using layout.key (order.length - 1) hlastBound
  have hkey : read raw (vectorKey initialMap.keys index) =
      some removed.val := by
    simpa [htarget] using layout.key index htargetBound
  have hvalue : read raw (vectorKey initialMap.values index) =
      some (Borsh.encodeMetadata oldValue) := by
    simpa [htarget] using layout.value index htargetBound
  have hlastValue : read raw (vectorKey initialMap.values (order.length - 1)) =
      some (Borsh.encodeMetadata movedValue) := by
    simpa [hlast] using layout.value (order.length - 1) hlastBound
  exact map_remove_middle_general raw order removed moved index oldValue
    movedValue hmiddle horderBound hdifferent hindex hlastKey
    (metadata_middle_index_preserves_vector raw removed moved index index
      initialMap.keys (by decide) removed.val hkey)
    (metadata_middle_index_preserves_vector raw removed moved index
      (order.length - 1) initialMap.keys (by decide) moved.val hlastKey)
    (metadata_middle_keys_preserves_value raw removed moved index
      order.length index (Borsh.encodeMetadata oldValue) hvalue)
    (metadata_middle_keys_preserves_value raw removed moved index
      order.length (order.length - 1) (Borsh.encodeMetadata movedValue)
      hlastValue) hbounded

def metadataMiddleDeletedRaw (raw : Raw) (order : List (Hash × Metadata))
    (removed moved : Hash) (index : Nat) (movedValue : Metadata) : Raw :=
  write
    (metadataMiddleValuesRaw raw removed moved index order.length movedValue)
    metadataKey (Borsh.encodeMap (metadataReducedHeader order))

def metadataSwapOrder (order : List (Hash × Metadata)) (index : Nat)
    (moved : Hash) (movedValue : Metadata) : List (Hash × Metadata) :=
  (order.take (order.length - 1)).set index (moved, movedValue)

theorem mem_set_fresh_cases {α : Type} (items : List α) (index : Nat)
    (replacement item : α) (hmem : item ∈ items.set index replacement) :
    item = replacement ∨ item ∈ items := by
  induction items generalizing index with
  | nil =>
    simp at hmem
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at hmem
      rcases hmem with he | ht
      · exact Or.inl he
      · exact Or.inr (by simp [ht])
    | succ index =>
      simp only [List.set_cons_succ, List.mem_cons] at hmem
      rcases hmem with he | ht
      · exact Or.inr (by simp [he])
      · rcases ih index ht with hr | ho
        · exact Or.inl hr
        · exact Or.inr (by simp [ho])

theorem nodup_set_fresh {α : Type} (items : List α) (index : Nat)
    (replacement : α) (hnodup : items.Nodup)
    (hfresh : replacement ∉ items) :
    (items.set index replacement).Nodup := by
  induction items generalizing index with
  | nil => simp
  | cons head tail ih =>
    have hhead : head ∉ tail := (List.nodup_cons.mp hnodup).1
    have htail : tail.Nodup := (List.nodup_cons.mp hnodup).2
    have hfreshTail : replacement ∉ tail := by
      intro hm
      exact hfresh (by simp [hm])
    cases index with
    | zero =>
      simp only [List.set_cons_zero, List.nodup_cons]
      exact ⟨hfreshTail, htail⟩
    | succ index =>
      simp only [List.set_cons_succ, List.nodup_cons]
      constructor
      · intro hm
        rcases mem_set_fresh_cases tail index replacement head hm with he | ht
        · exact hfresh (by simp [he])
        · exact hhead ht
      · exact ih index htail hfreshTail

theorem metadata_swap_order_length (order : List (Hash × Metadata))
    (index : Nat) (moved : Hash) (movedValue : Metadata) :
    (metadataSwapOrder order index moved movedValue).length = order.length - 1 := by
  simp [metadataSwapOrder, Nat.sub_le]

theorem metadata_swap_order_at_target (order : List (Hash × Metadata))
    (index : Nat) (moved : Hash) (movedValue : Metadata)
    (hmiddle : index + 1 < order.length) :
    (metadataSwapOrder order index moved movedValue)[index]? =
      some (moved, movedValue) := by
  have hi : index < (order.take (order.length - 1)).length := by
    simp [Nat.sub_le]
    omega
  exact List.getElem?_set_self hi

theorem metadata_swap_order_at_other (order : List (Hash × Metadata))
    (index slot : Nat) (moved : Hash) (movedValue : Metadata)
    (hslot : slot < order.length - 1) (hne : slot ≠ index) :
    (metadataSwapOrder order index moved movedValue)[slot]? = order[slot]? := by
  rw [metadataSwapOrder, List.getElem?_set_ne (Ne.symm hne),
    List.getElem?_take]
  simp [hslot]

theorem metadata_swap_order_header (order : List (Hash × Metadata))
    (index : Nat) (moved : Hash) (movedValue : Metadata) :
    Spec.metadataHeader (metadataSwapOrder order index moved movedValue) =
      metadataReducedHeader order := by
  simp [Spec.metadataHeader, metadataReducedHeader, metadata_swap_order_length]

theorem metadata_swap_order_unique (raw : Raw)
    (order : List (Hash × Metadata)) (index : Nat)
    (moved : Hash) (movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hlast : order[order.length - 1]? = some (moved, movedValue)) :
    ((metadataSwapOrder order index moved movedValue).map Prod.fst).Nodup := by
  let front := order.take (order.length - 1)
  have hsplit : order = front ++ [(moved, movedValue)] :=
    metadata_order_split_last order moved movedValue hlast
  have hnodup : (front.map Prod.fst ++ [moved]).Nodup := by
    simpa [hsplit, List.map_append] using layout.unique
  have hparts := List.nodup_append.mp hnodup
  have hfresh : moved ∉ front.map Prod.fst := by
    intro hm
    exact (hparts.2.2 moved hm moved (by simp)) rfl
  have hset := nodup_set_fresh (front.map Prod.fst) index moved hparts.1 hfresh
  simpa [metadataSwapOrder, front, List.map_set, List.map_take] using hset

/-- Replacing one unique hash with a fresh hash changes only the two affected
lookups. This is the list-level counterpart of the SDK's index-key writes. -/
theorem find_hash_set_fresh (front : List (Hash × Metadata))
    (index : Nat) (removed moved : Hash)
    (oldValue movedValue : Metadata)
    (hnodup : (front.map Prod.fst).Nodup)
    (hfresh : moved ∉ front.map Prod.fst)
    (htarget : front[index]? = some (removed, oldValue))
    (hdifferent : moved ≠ removed) (query : Hash) :
    Spec.findHash (front.set index (moved, movedValue)) query =
      if query = moved then some index
      else if query = removed then none
      else Spec.findHash front query := by
  induction front generalizing index with
  | nil =>
    cases index <;> simp at htarget
  | cons head tail ih =>
    have hheadNodup : head.1 ∉ tail.map Prod.fst := by
      simpa using (List.nodup_cons.mp hnodup).1
    have htailNodup : (tail.map Prod.fst).Nodup := by
      simpa using (List.nodup_cons.mp hnodup).2
    have hmovedNeHead : moved ≠ head.1 := by
      intro he
      exact hfresh (by simp [he])
    have hmovedFresh : moved ∉ tail.map Prod.fst := by
      intro hm
      exact hfresh (by simp [hm])
    cases index with
    | zero =>
      simp at htarget
      subst head
      have hremovedTail : removed ∉ tail.map Prod.fst := by
        simpa using hheadNodup
      have hremovedAbsent := find_hash_not_mem_none tail removed hremovedTail
      by_cases hm : query = moved
      · subst query
        simp [Spec.findHash]
      · by_cases hr : query = removed
        · subst query
          have hne : moved.val ≠ removed.val := by
            intro he
            exact hdifferent (Subtype.ext he)
          simp [Spec.findHash, hne, hremovedAbsent, hm]
        · have hneMoved : moved.val ≠ query.val := by
            intro he
            exact hm (Subtype.ext he.symm)
          have hneRemoved : removed.val ≠ query.val := by
            intro he
            exact hr (Subtype.ext he.symm)
          simp [Spec.findHash, hneMoved, hneRemoved, hm, hr]
    | succ index =>
      have htargetTail : tail[index]? = some (removed, oldValue) := by
        simpa using htarget
      have hremovedNeHead : removed ≠ head.1 := by
        intro he
        have hmem : removed ∈ tail.map Prod.fst := by
          have hm : (removed, oldValue) ∈ tail :=
            List.mem_of_getElem? htargetTail
          exact List.mem_map_of_mem hm
        exact hheadNodup (he ▸ hmem)
      have ih' := ih index htailNodup hmovedFresh htargetTail
      by_cases hh : head.1 = query
      · subst query
        have hqm : head.1 ≠ moved := Ne.symm hmovedNeHead
        have hqr : head.1 ≠ removed := Ne.symm hremovedNeHead
        simp [Spec.findHash, hqm, hqr]
      · have hheadVal : head.1.val ≠ query.val := by
          intro he
          exact hh (Subtype.ext he)
        simp only [List.set_cons_succ, Spec.findHash]
        simp [hheadVal, ih']
        by_cases hm : query = moved
        · simp [hm]
        · by_cases hr : query = removed
          · simp [hr]
          · simp [hm, hr]

theorem find_hash_swap_order (raw : Raw)
    (order : List (Hash × Metadata)) (index : Nat)
    (removed moved query : Hash) (oldValue movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (htarget : order[index]? = some (removed, oldValue))
    (hlast : order[order.length - 1]? = some (moved, movedValue))
    (hdifferent : moved ≠ removed) :
    Spec.findHash (metadataSwapOrder order index moved movedValue) query =
      if query = moved then some index
      else if query = removed then none
      else Spec.findHash order query := by
  let front := order.take (order.length - 1)
  have hsplit : order = front ++ [(moved, movedValue)] :=
    metadata_order_split_last order moved movedValue hlast
  have hnodup : (front.map Prod.fst ++ [moved]).Nodup := by
    simpa [hsplit, List.map_append] using layout.unique
  have hparts := List.nodup_append.mp hnodup
  have hfresh : moved ∉ front.map Prod.fst := by
    intro hm
    exact (hparts.2.2 moved hm moved (by simp)) rfl
  have htargetFront : front[index]? = some (removed, oldValue) := by
    rw [show front[index]? = order[index]? by
      simp [front, show index < order.length - 1 by omega]]
    exact htarget
  have hset := find_hash_set_fresh front index removed moved oldValue movedValue
    hparts.1 hfresh htargetFront hdifferent query
  unfold metadataSwapOrder
  rw [hset]
  by_cases hm : query = moved
  · simp [hm]
  · have hfind := find_hash_append_other front moved query movedValue (Ne.symm hm)
    rw [← hsplit] at hfind
    rw [hfind]

theorem metadata_middle_key_slot (raw : Raw)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index slot : Nat) (movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (hbound : order.length < 256 ^ 8)
    (hslot : slot < (metadataSwapOrder order index moved movedValue).length) :
    read (metadataMiddleDeletedRaw raw order removed moved index movedValue)
      (vectorKey initialMap.keys slot) =
      ((metadataSwapOrder order index moved movedValue)[slot]?).map
        (fun entry => entry.1.val) := by
  have hslot' : slot < order.length - 1 := by
    simpa [metadata_swap_order_length] using hslot
  have hslotOld : slot < order.length := by omega
  have hheader : vectorKey initialMap.keys slot ≠ metadataKey := by
    intro he
    have hlen := congrArg List.length he
    simp [vectorKey, initialMap, metadataKey] at hlen
  have hlastKey : vectorKey initialMap.keys slot ≠
      vectorKey initialMap.keys (order.length - 1) := by
    intro he
    have hs : slot < 256 ^ 8 := by omega
    have hl : order.length - 1 < 256 ^ 8 := by omega
    have heq := vector_key_injective_bounded initialMap.keys slot
      (order.length - 1) hs hl he
    omega
  have hindexKey : vectorKey initialMap.keys slot ≠
      mapIndexKey initialMap removed :=
    vector_key_not_metadata_index initialMap.keys slot removed (by decide)
  have hmovedIndex : vectorKey initialMap.keys slot ≠
      mapIndexKey initialMap moved :=
    vector_key_not_metadata_index initialMap.keys slot moved (by decide)
  unfold metadataMiddleDeletedRaw metadataMiddleValuesRaw
    metadataMiddleKeysRaw metadataMiddleIndexRaw
  rw [read_write_other _ _ _ _ hheader]
  rw [read_write_other _ _ _ _ (by simp [vectorKey, initialMap])]
  rw [read_remove_other _ _ _ (by simp [vectorKey, initialMap])]
  by_cases he : slot = index
  · subst slot
    rw [read_write_self]
    rw [metadata_swap_order_at_target order index moved movedValue hmiddle]
    rfl
  · have htargetKey : vectorKey initialMap.keys slot ≠
        vectorKey initialMap.keys index := by
      intro heq
      have hs : slot < 256 ^ 8 := by omega
      have hi : index < 256 ^ 8 := by omega
      exact he (vector_key_injective_bounded initialMap.keys slot index
        hs hi heq)
    rw [read_write_other _ _ _ _ htargetKey]
    rw [read_remove_other _ _ _ hlastKey]
    rw [read_write_other _ _ _ _ hmovedIndex]
    rw [read_remove_other _ _ _ hindexKey]
    rw [metadata_swap_order_at_other order index slot moved movedValue hslot' he]
    exact layout.key slot hslotOld

theorem metadata_middle_value_slot (raw : Raw)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index slot : Nat) (movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (hbound : order.length < 256 ^ 8)
    (hslot : slot < (metadataSwapOrder order index moved movedValue).length) :
    read (metadataMiddleDeletedRaw raw order removed moved index movedValue)
      (vectorKey initialMap.values slot) =
      ((metadataSwapOrder order index moved movedValue)[slot]?).map
        (fun entry => Borsh.encodeMetadata entry.2) := by
  have hslot' : slot < order.length - 1 := by
    simpa [metadata_swap_order_length] using hslot
  have hslotOld : slot < order.length := by omega
  have hheader : vectorKey initialMap.values slot ≠ metadataKey := by
    intro he
    have hlen := congrArg List.length he
    simp [vectorKey, initialMap, metadataKey] at hlen
  have hlastValue : vectorKey initialMap.values slot ≠
      vectorKey initialMap.values (order.length - 1) := by
    intro he
    have hs : slot < 256 ^ 8 := by omega
    have hl : order.length - 1 < 256 ^ 8 := by omega
    have heq := vector_key_injective_bounded initialMap.values slot
      (order.length - 1) hs hl he
    omega
  have hindexKey : vectorKey initialMap.values slot ≠
      mapIndexKey initialMap removed :=
    vector_key_not_metadata_index initialMap.values slot removed (by decide)
  have hmovedIndex : vectorKey initialMap.values slot ≠
      mapIndexKey initialMap moved :=
    vector_key_not_metadata_index initialMap.values slot moved (by decide)
  unfold metadataMiddleDeletedRaw metadataMiddleValuesRaw
    metadataMiddleKeysRaw metadataMiddleIndexRaw
  rw [read_write_other _ _ _ _ hheader]
  by_cases he : slot = index
  · subst slot
    rw [read_write_self]
    rw [metadata_swap_order_at_target order index moved movedValue hmiddle]
    rfl
  · have htargetValue : vectorKey initialMap.values slot ≠
        vectorKey initialMap.values index := by
      intro heq
      have hs : slot < 256 ^ 8 := by omega
      have hi : index < 256 ^ 8 := by omega
      exact he (vector_key_injective_bounded initialMap.values slot index
        hs hi heq)
    rw [read_write_other _ _ _ _ htargetValue]
    rw [read_remove_other _ _ _ hlastValue]
    rw [read_write_other _ _ _ _ (by simp [vectorKey, initialMap])]
    rw [read_remove_other _ _ _ (by simp [vectorKey, initialMap])]
    rw [read_write_other _ _ _ _ hmovedIndex]
    rw [read_remove_other _ _ _ hindexKey]
    rw [metadata_swap_order_at_other order index slot moved movedValue hslot' he]
    exact layout.value slot hslotOld

theorem metadata_middle_index_lookup (raw : Raw)
    (order : List (Hash × Metadata)) (removed moved query : Hash)
    (index : Nat) (movedValue : Metadata) :
    read (metadataMiddleDeletedRaw raw order removed moved index movedValue)
      (mapIndexKey initialMap query) =
      if query = moved then some (leBytes 8 index)
      else if query = removed then none
      else read raw (mapIndexKey initialMap query) := by
  have hheader : mapIndexKey initialMap query ≠ metadataKey := by
    intro he
    have hlen := congrArg List.length he
    simp [mapIndexKey, initialMap, metadataKey, query.property] at hlen
  have hvalueTarget : mapIndexKey initialMap query ≠
      vectorKey initialMap.values index :=
    (vector_key_not_metadata_index initialMap.values index query (by decide)).symm
  have hvalueLast : mapIndexKey initialMap query ≠
      vectorKey initialMap.values (order.length - 1) :=
    (vector_key_not_metadata_index initialMap.values (order.length - 1)
      query (by decide)).symm
  have hkeyTarget : mapIndexKey initialMap query ≠
      vectorKey initialMap.keys index :=
    (vector_key_not_metadata_index initialMap.keys index query (by decide)).symm
  have hkeyLast : mapIndexKey initialMap query ≠
      vectorKey initialMap.keys (order.length - 1) :=
    (vector_key_not_metadata_index initialMap.keys (order.length - 1)
      query (by decide)).symm
  unfold metadataMiddleDeletedRaw metadataMiddleValuesRaw
    metadataMiddleKeysRaw metadataMiddleIndexRaw
  rw [read_write_other _ _ _ _ hheader]
  rw [read_write_other _ _ _ _ hvalueTarget]
  rw [read_remove_other _ _ _ hvalueLast]
  rw [read_write_other _ _ _ _ hkeyTarget]
  rw [read_remove_other _ _ _ hkeyLast]
  by_cases hm : query = moved
  · subst query
    simp [read_write_self]
  · have hmKey : mapIndexKey initialMap query ≠
        mapIndexKey initialMap moved := by
      intro he
      exact hm (canonical_map_index_injective query moved he)
    rw [read_write_other _ _ _ _ hmKey]
    by_cases hr : query = removed
    · subst query
      simp [hm, read_remove_self]
    · have hrKey : mapIndexKey initialMap query ≠
          mapIndexKey initialMap removed := by
        intro he
        exact hr (canonical_map_index_injective query removed he)
      rw [read_remove_other _ _ _ hrKey]
      simp [hm, hr]

theorem metadata_middle_delete_preserves_layout (raw : Raw)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index : Nat) (oldValue movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (hbound : order.length < 256 ^ 8)
    (hdifferent : moved.val ≠ removed.val)
    (htarget : order[index]? = some (removed, oldValue))
    (hlast : order[order.length - 1]? = some (moved, movedValue)) :
    Spec.MetadataLayout
      (metadataMiddleDeletedRaw raw order removed moved index movedValue)
      (metadataSwapOrder order index moved movedValue) := by
  have hne : moved ≠ removed := by
    intro he
    exact hdifferent (congrArg Subtype.val he)
  constructor
  · exact metadata_swap_order_unique raw order index moved movedValue layout hlast
  · rw [metadata_swap_order_header]
    exact read_write_self _ _ _
  · intro query
    rw [metadata_middle_index_lookup]
    rw [find_hash_swap_order raw order index removed moved query oldValue
      movedValue layout hmiddle htarget hlast hne]
    by_cases hm : query = moved
    · simp [hm]
    · by_cases hr : query = removed
      · simp [hr]
      · simpa [hm, hr] using layout.index query
  · intro slot hslot
    exact metadata_middle_key_slot raw order removed moved index slot
      movedValue layout hmiddle hbound hslot
  · intro slot hslot
    exact metadata_middle_value_slot raw order removed moved index slot
      movedValue layout hmiddle hbound hslot

theorem metadata_middle_delete_preserves_state (raw : Raw)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index : Nat) (movedValue : Metadata) :
    read (metadataMiddleDeletedRaw raw order removed moved index movedValue)
      stateKey = read raw stateKey := by
  have hremoved : stateKey ≠ mapIndexKey initialMap removed := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, removed.property] at hlen
  have hmoved : stateKey ≠ mapIndexKey initialMap moved := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, moved.property] at hlen
  have hkeyTarget : stateKey ≠ vectorKey initialMap.keys index := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  have hkeyLast : stateKey ≠
      vectorKey initialMap.keys (order.length - 1) := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  have hvalueTarget : stateKey ≠ vectorKey initialMap.values index := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  have hvalueLast : stateKey ≠
      vectorKey initialMap.values (order.length - 1) := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  unfold metadataMiddleDeletedRaw metadataMiddleValuesRaw
    metadataMiddleKeysRaw metadataMiddleIndexRaw
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ metadataKey)]
  rw [read_write_other _ _ _ _ hvalueTarget]
  rw [read_remove_other _ _ _ hvalueLast]
  rw [read_write_other _ _ _ _ hkeyTarget]
  rw [read_remove_other _ _ _ hkeyLast]
  rw [read_write_other _ _ _ _ hmoved]
  rw [read_remove_other _ _ _ hremoved]

/-- Source-level exported deletion follows the SDK's nonfinal swap path for
any bounded canonical map satisfying the explicit target and last-slot facts. -/
theorem delete_metadata_middle_entry_general (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index : Nat) (oldValue movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (horderBound : order.length < 256 ^ 8)
    (hdifferent : moved.val ≠ removed.val)
    (hindex : read raw (mapIndexKey initialMap removed) = some (leBytes 8 index))
    (htarget : order[index]? = some (removed, oldValue))
    (hlast : order[order.length - 1]? = some (moved, movedValue))
    (hbounded : Spec.MetadataBounded oldValue)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.deleteMetadata removed) =
      .ok ⟨metadataMiddleDeletedRaw raw order removed moved index movedValue,
        [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader order)) =
      some (Spec.metadataHeader order) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderBound
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderBound
    · simp [Spec.metadataHeader, initialMap]
  have hremove := map_remove_middle_from_layout raw order removed moved index
    oldValue movedValue layout hmiddle horderBound hdifferent hindex htarget
    hlast hbounded
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, loadMap, layout.header, hmap, hremove, metadataMiddleDeletedRaw,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem delete_metadata_middle_entry_preserves_layout (cfg : Config)
    (raw : Raw) (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index : Nat) (oldValue movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (hbound : order.length < 256 ^ 8)
    (hdifferent : moved.val ≠ removed.val)
    (hindex : read raw (mapIndexKey initialMap removed) = some (leBytes 8 index))
    (htarget : order[index]? = some (removed, oldValue))
    (hlast : order[order.length - 1]? = some (moved, movedValue))
    (hbounded : Spec.MetadataBounded oldValue)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata removed) = .ok out) :
    Spec.MetadataLayout out.raw
      (metadataSwapOrder order index moved movedValue) := by
  rw [delete_metadata_middle_entry_general cfg raw env setHeader order
    removed moved index oldValue movedValue layout hmiddle hbound hdifferent
    hindex htarget hlast hbounded hstate hsetIndex hsetLength hsetPrefix
    howner] at hstep
  cases hstep
  exact metadata_middle_delete_preserves_layout raw order removed moved index
    oldValue movedValue layout hmiddle hbound hdifferent htarget hlast

theorem metadata_swap_order_bounded (order : List (Hash × Metadata))
    (index : Nat) (moved : Hash) (movedValue : Metadata)
    (hlast : order[order.length - 1]? = some (moved, movedValue))
    (hbounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2) :
    ∀ entry ∈ metadataSwapOrder order index moved movedValue,
      Spec.MetadataBounded entry.2 := by
  intro entry hmem
  rcases mem_set_fresh_cases (order.take (order.length - 1)) index
    (moved, movedValue) entry hmem with he | ho
  · subst entry
    exact hbounded (moved, movedValue) (List.mem_of_getElem? hlast)
  · exact hbounded entry (List.mem_of_mem_take ho)

theorem delete_metadata_middle_entry_getter (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (removed moved : Hash)
    (index : Nat) (oldValue movedValue : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hmiddle : index + 1 < order.length)
    (hbound : order.length < 256 ^ 8)
    (hdifferent : moved.val ≠ removed.val)
    (hindex : read raw (mapIndexKey initialMap removed) = some (leBytes 8 index))
    (htarget : order[index]? = some (removed, oldValue))
    (hlast : order[order.length - 1]? = some (moved, movedValue))
    (hbounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata removed) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata
        (metadataSwapOrder order index moved movedValue)⟩ := by
  have hboundOld : Spec.MetadataBounded oldValue :=
    hbounded (removed, oldValue) (List.mem_of_getElem? htarget)
  rw [delete_metadata_middle_entry_general cfg raw env setHeader order
    removed moved index oldValue movedValue layout hmiddle hbound hdifferent
    hindex htarget hlast hboundOld hstate hsetIndex hsetLength hsetPrefix
    howner] at hstep
  cases hstep
  have hstate' : read
      (metadataMiddleDeletedRaw raw order removed moved index movedValue)
      stateKey = some (Borsh.encodeSet setHeader) := by
    rw [metadata_middle_delete_preserves_state]
    exact hstate
  have hpostLength :
      (metadataSwapOrder order index moved movedValue).length < 256 ^ 8 := by
    rw [metadata_swap_order_length]
    omega
  exact metadata_getter_matches_layout cfg _ env setHeader
    (metadataSwapOrder order index moved movedValue)
    hstate' hsetIndex hsetLength hsetPrefix
    (metadata_middle_delete_preserves_layout raw order removed moved index
      oldValue movedValue layout hmiddle hbound hdifferent htarget hlast)
    hpostLength (metadata_swap_order_bounded order index moved movedValue
      hlast hbounded)

theorem map_remove_tail_general (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (hcount : 2 ≤ order.length)
    (horderBound : order.length < 256 ^ 8)
    (hindex : read raw (mapIndexKey initialMap hash) =
      some (leBytes 8 (order.length - 1)))
    (hkey : read raw (vectorKey initialMap.keys (order.length - 1)) =
      some hash.val)
    (hvalue : read raw (vectorKey initialMap.values (order.length - 1)) =
      some (Borsh.encodeMetadata value))
    (hbounded : Spec.MetadataBounded value) :
    (mapRemove (Spec.metadataHeader order) hash).run raw =
      .ok (metadataReducedHeader order,
        metadataTailRemovedRaw raw hash order.length) := by
  have hkeyAfter : read (remove raw (mapIndexKey initialMap hash))
      (vectorKey initialMap.keys (order.length - 1)) = some hash.val := by
    rw [read_remove_other _ _ _
      (vector_key_not_metadata_index initialMap.keys (order.length - 1)
        hash (by decide))]
    exact hkey
  have hvalueAfter : read
      (remove (remove raw (mapIndexKey initialMap hash))
        (vectorKey initialMap.keys (order.length - 1)))
      (vectorKey initialMap.values (order.length - 1)) =
      some (Borsh.encodeMetadata value) := by
    rw [read_remove_other _ _ _ (by simp [vectorKey, initialMap])]
    rw [read_remove_other _ _ _
      (vector_key_not_metadata_index initialMap.values (order.length - 1)
        hash (by decide))]
    exact hvalue
  have hlastGet : (vectorGet (Spec.metadataHeader order).keys
      (order.length - 1)).run raw = .ok (some hash.val, raw) := by
    apply vector_get_present
    · simpa [Spec.metadataHeader] using (show order.length - 1 < order.length by omega)
    · simpa [Spec.metadataHeader, vectorKey] using hkey
  have hkeys := vector_swap_remove_last
    (Spec.metadataHeader order).keys
    (remove raw (mapIndexKey initialMap hash))
    (order.length - 1) hash.val
    (by simp [Spec.metadataHeader]; omega)
    (by simpa [Spec.metadataHeader, vectorKey] using hkeyAfter)
  have hvalues := vector_swap_remove_last
    (Spec.metadataHeader order).values
    (remove (remove raw (mapIndexKey initialMap hash))
      (vectorKey initialMap.keys (order.length - 1)))
    (order.length - 1) (Borsh.encodeMetadata value)
    (by simp [Spec.metadataHeader]; omega)
    (by simpa [Spec.metadataHeader, vectorKey] using hvalueAfter)
  have hdecode := exact_natural_encode 8 (order.length - 1)
    (show order.length - 1 < 256 ^ 8 by omega)
  have hmetadata := exact_metadata_encode_bounded value hbounded.1 hbounded.2
  have hnotOne : order.length ≠ 1 := by omega
  have hpositive : 0 < order.length := by omega
  simp [Spec.metadataHeader, initialMap, mapIndexKey, vectorKey] at hindex hlastGet hkeys hvalues
  simp [mapRemove, Spec.metadataHeader, initialMap, mapIndexKey, vectorKey,
    hindex, hlastGet, hdecode, hkeys, hvalues, hmetadata,
    metadataReducedHeader, metadataTailRemovedRaw, mapLength,
    load, erase, require, expect, Bind.bind, Pure.pure,
    Tx.run_bind, Tx.bind, Tx.run, Except.bind, hnotOne, hpositive]

def metadataTailDeletedRaw (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash) : Raw :=
  write (metadataTailRemovedRaw raw hash order.length) metadataKey
    (Borsh.encodeMap (metadataReducedHeader order))

theorem delete_metadata_tail_entry_general (cfg : Config) (raw : Raw)
    (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (hcount : 2 ≤ order.length)
    (horderBound : order.length < 256 ^ 8)
    (hindex : read raw (mapIndexKey initialMap hash) =
      some (leBytes 8 (order.length - 1)))
    (hkey : read raw (vectorKey initialMap.keys (order.length - 1)) =
      some hash.val)
    (hvalue : read raw (vectorKey initialMap.values (order.length - 1)) =
      some (Borsh.encodeMetadata value))
    (hbounded : Spec.MetadataBounded value)
    (hmetadata : read raw metadataKey = some
      (Borsh.encodeMap (Spec.metadataHeader order)))
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw)) :
    step cfg raw env (.deleteMetadata hash) =
      .ok ⟨metadataTailDeletedRaw raw order hash, [], .unit⟩ := by
  have hdecode := exact_set_encode setHeader hsetIndex hsetLength hsetPrefix
  have hmap : Borsh.exact Borsh.mapHeader
      (Borsh.encodeMap (Spec.metadataHeader order)) =
      some (Spec.metadataHeader order) := by
    apply exact_map_encode
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderBound
    · simp [Spec.metadataHeader, initialMap]
    · simpa [Spec.metadataHeader] using horderBound
    · simp [Spec.metadataHeader, initialMap]
  have hremove := map_remove_tail_general raw order hash value hcount
    horderBound hindex hkey hvalue hbounded
  simp [step, entry, loadFactory, assertOwner, hstate, hdecode, howner,
    body, loadMap, hmetadata, hmap, hremove, metadataTailDeletedRaw,
    Call.private, Call.rejectDeposit, Call.isNew, Call.ownerOnly,
    Call.saveHeader, require, expect, done, load, save,
    Bind.bind, Pure.pure, Tx.run_bind, Tx.bind, Tx.run, Except.bind]

theorem metadata_tail_delete_preserves_layout (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (horderBound : order.length < 256 ^ 8)
    (hlast : order[order.length - 1]? = some (hash, value)) :
    Spec.MetadataLayout (metadataTailDeletedRaw raw order hash)
      (order.take (order.length - 1)) := by
  let front := order.take (order.length - 1)
  have hsplit : order = front ++ [(hash, value)] :=
    metadata_order_split_last order hash value hlast
  have hlen : front.length = order.length - 1 := by
    simp [front, Nat.sub_le]
  have hnodup : (front.map Prod.fst ++ [hash]).Nodup := by
    simpa [hsplit, List.map_append] using layout.unique
  have hparts := List.nodup_append.mp hnodup
  have hnotmem : hash ∉ front.map Prod.fst := by
    intro hmem
    exact (hparts.2.2 hash hmem hash (by simp)) rfl
  have hfindAbsent : Spec.findHash front hash = none :=
    find_hash_not_mem_none front hash hnotmem
  constructor
  · exact hparts.1
  · unfold metadataTailDeletedRaw
    rw [read_write_self]
    rw [metadata_reduced_header_eq_take]
  · intro query
    have hheader : mapIndexKey initialMap query ≠ metadataKey := by
      intro he
      have hlength := congrArg List.length he
      simp [mapIndexKey, initialMap, metadataKey, query.property] at hlength
    have hkey : mapIndexKey initialMap query ≠
        vectorKey initialMap.keys (order.length - 1) :=
      (vector_key_not_metadata_index initialMap.keys (order.length - 1)
        query (by decide)).symm
    have hvalue : mapIndexKey initialMap query ≠
        vectorKey initialMap.values (order.length - 1) :=
      (vector_key_not_metadata_index initialMap.values (order.length - 1)
        query (by decide)).symm
    unfold metadataTailDeletedRaw metadataTailRemovedRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_remove_other _ _ _ hvalue]
    rw [read_remove_other _ _ _ hkey]
    by_cases he : query = hash
    · subst query
      rw [read_remove_self]
      change none = (Spec.findHash front hash).map (leBytes 8)
      simp [hfindAbsent]
    · have hnotIndex : mapIndexKey initialMap query ≠
          mapIndexKey initialMap hash := by
        intro heq
        exact he (canonical_map_index_injective query hash heq)
      rw [read_remove_other _ _ _ hnotIndex]
      have hfind := find_hash_append_other front hash query value (Ne.symm he)
      rw [← hsplit] at hfind
      rw [← hfind]
      exact layout.index query
  · intro i hi
    have hiPrefix : i < front.length := hi
    have hiOrder : i < order.length := by omega
    have hheader : vectorKey initialMap.keys i ≠ metadataKey := by
      intro he
      have hlength := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlength
    have hvalue : vectorKey initialMap.keys i ≠
        vectorKey initialMap.values (order.length - 1) := by
      simp [vectorKey, initialMap]
    have hkey : vectorKey initialMap.keys i ≠
        vectorKey initialMap.keys (order.length - 1) := by
      intro heq
      have hiBound : i < 256 ^ 8 := Nat.lt_trans hiOrder horderBound
      have hlastBound : order.length - 1 < 256 ^ 8 := by omega
      have heqIndex := vector_key_injective_bounded initialMap.keys i
        (order.length - 1) hiBound hlastBound heq
      omega
    have hindex : vectorKey initialMap.keys i ≠ mapIndexKey initialMap hash :=
      vector_key_not_metadata_index initialMap.keys i hash (by decide)
    unfold metadataTailDeletedRaw metadataTailRemovedRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_remove_other _ _ _ hvalue]
    rw [read_remove_other _ _ _ hkey]
    rw [read_remove_other _ _ _ hindex]
    have hread := layout.key i hiOrder
    rw [hsplit] at hread
    rw [List.getElem?_append_left hiPrefix] at hread
    simpa [front] using hread

  · intro i hi
    have hiPrefix : i < front.length := hi
    have hiOrder : i < order.length := by omega
    have hheader : vectorKey initialMap.values i ≠ metadataKey := by
      intro he
      have hlength := congrArg List.length he
      simp [vectorKey, initialMap, metadataKey] at hlength
    have hvalue : vectorKey initialMap.values i ≠
        vectorKey initialMap.values (order.length - 1) := by
      intro heq
      have hiBound : i < 256 ^ 8 := Nat.lt_trans hiOrder horderBound
      have hlastBound : order.length - 1 < 256 ^ 8 := by omega
      have heqIndex := vector_key_injective_bounded initialMap.values i
        (order.length - 1) hiBound hlastBound heq
      omega
    have hkey : vectorKey initialMap.values i ≠
        vectorKey initialMap.keys (order.length - 1) := by
      simp [vectorKey, initialMap]
    have hindex : vectorKey initialMap.values i ≠ mapIndexKey initialMap hash :=
      vector_key_not_metadata_index initialMap.values i hash (by decide)
    unfold metadataTailDeletedRaw metadataTailRemovedRaw
    rw [read_write_other _ _ _ _ hheader]
    rw [read_remove_other _ _ _ hvalue]
    rw [read_remove_other _ _ _ hkey]
    rw [read_remove_other _ _ _ hindex]
    have hread := layout.value i hiOrder
    rw [hsplit] at hread
    rw [List.getElem?_append_left hiPrefix] at hread
    simpa [front] using hread

theorem delete_metadata_tail_entry_preserves_layout (cfg : Config)
    (raw : Raw) (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hcount : 2 ≤ order.length)
    (horderBound : order.length < 256 ^ 8)
    (hlast : order[order.length - 1]? = some (hash, value))
    (hbounded : Spec.MetadataBounded value)
    (hindex : read raw (mapIndexKey initialMap hash) =
      some (leBytes 8 (order.length - 1)))
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata hash) = .ok out) :
    Spec.MetadataLayout out.raw (order.take (order.length - 1)) := by
  have hlastBound : order.length - 1 < order.length := by omega
  have hkey : read raw (vectorKey initialMap.keys (order.length - 1)) =
      some hash.val := by
    simpa [hlast] using layout.key (order.length - 1) hlastBound
  have hvalue : read raw (vectorKey initialMap.values (order.length - 1)) =
      some (Borsh.encodeMetadata value) := by
    simpa [hlast] using layout.value (order.length - 1) hlastBound
  rw [delete_metadata_tail_entry_general cfg raw env setHeader order hash
    value hcount horderBound hindex hkey hvalue hbounded layout.header
    hstate hsetIndex hsetLength hsetPrefix howner] at hstep
  cases hstep
  exact metadata_tail_delete_preserves_layout raw order hash value layout
    horderBound hlast

theorem metadata_tail_delete_preserves_state (raw : Raw)
    (order : List (Hash × Metadata)) (hash : Hash) :
    read (metadataTailDeletedRaw raw order hash) stateKey = read raw stateKey := by
  have hindex : stateKey ≠ mapIndexKey initialMap hash := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, mapIndexKey, initialMap, hash.property] at hlen
  have hkey : stateKey ≠ vectorKey initialMap.keys (order.length - 1) := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  have hvalue : stateKey ≠ vectorKey initialMap.values (order.length - 1) := by
    intro he
    have hlen := congrArg List.length he
    simp [stateKey, vectorKey, initialMap] at hlen
  unfold metadataTailDeletedRaw metadataTailRemovedRaw
  rw [read_write_other _ _ _ _ (by decide : stateKey ≠ metadataKey)]
  rw [read_remove_other _ _ _ hvalue]
  rw [read_remove_other _ _ _ hkey]
  rw [read_remove_other _ _ _ hindex]

theorem delete_metadata_tail_then_get_general (cfg : Config)
    (raw : Raw) (env : Env) (setHeader : SetHeader)
    (order : List (Hash × Metadata)) (hash : Hash) (value : Metadata)
    (layout : Spec.MetadataLayout raw order)
    (hcount : 2 ≤ order.length)
    (horderBound : order.length < 256 ^ 8)
    (hlast : order[order.length - 1]? = some (hash, value))
    (hbounded : ∀ entry ∈ order, Spec.MetadataBounded entry.2)
    (hindex : read raw (mapIndexKey initialMap hash) =
      some (leBytes 8 (order.length - 1)))
    (hstate : read raw stateKey = some (Borsh.encodeSet setHeader))
    (hsetIndex : setHeader.indexPrefix.length < 256 ^ 4)
    (hsetLength : setHeader.elements.length < 256 ^ 8)
    (hsetPrefix : setHeader.elements.keyPrefix.length < 256 ^ 4)
    (howner : (getOwner env.current).run raw = .ok (env.predecessor, raw))
    (out : Outcome)
    (hstep : step cfg raw env (.deleteMetadata hash) = .ok out) :
    step cfg out.raw env .getMetadata =
      .ok ⟨out.raw, [], .metadata (order.take (order.length - 1))⟩ := by
  have hlastBound : order.length - 1 < order.length := by omega
  have hkey : read raw (vectorKey initialMap.keys (order.length - 1)) =
      some hash.val := by
    simpa [hlast] using layout.key (order.length - 1) hlastBound
  have hvalue : read raw (vectorKey initialMap.values (order.length - 1)) =
      some (Borsh.encodeMetadata value) := by
    simpa [hlast] using layout.value (order.length - 1) hlastBound
  have hlastValueBound := hbounded (hash, value) (List.mem_of_getElem? hlast)
  rw [delete_metadata_tail_entry_general cfg raw env setHeader order hash
    value hcount horderBound hindex hkey hvalue hlastValueBound layout.header
    hstate hsetIndex hsetLength hsetPrefix howner] at hstep
  cases hstep
  have hstate' : read (metadataTailDeletedRaw raw order hash) stateKey =
      some (Borsh.encodeSet setHeader) := by
    rw [metadata_tail_delete_preserves_state]
    exact hstate
  have hpostLength : (order.take (order.length - 1)).length < 256 ^ 8 := by
    exact Nat.lt_of_le_of_lt (List.length_take_le' ..) horderBound
  have hpostBounded : ∀ entry ∈ order.take (order.length - 1),
      Spec.MetadataBounded entry.2 := by
    intro entry hmem
    exact hbounded entry (List.mem_of_mem_take hmem)
  exact metadata_getter_matches_layout cfg _ env setHeader
    (order.take (order.length - 1)) hstate' hsetIndex hsetLength hsetPrefix
    (metadata_tail_delete_preserves_layout raw order hash value layout
      horderBound hlast) hpostLength hpostBounded
end SputnikFactory
