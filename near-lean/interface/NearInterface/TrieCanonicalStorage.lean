import NearInterface.TrieCanonicalLookup
import NearInterface.TrieOverlayStorage

/-!
# Canonical trie reads agree with boundary raw storage

The original context's WF provides account-local storage agreement and overlay
uniqueness. Canonical node-zero exclusion remains explicit; no base lookup,
dereference or complete host execution callback is assumed.
-/
namespace NearInterface
open Wasm Wasm.Near Near.TrieOverlay

/-- Every account-local canonical lookup succeeds, preserves the base/view,
and has precisely the presence of the raw list used by the VM. -/
theorem wf_canonical_reference (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key : Bytes) (accountNodes : Bool) (hnodes : ctx.trie.NonzeroNodes) :
    ∃ after pointer,
      getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes = .ok (after, pointer) ∧
      after.base = ctx.trie.base ∧ after.view = ctx.trie.view ∧
      pointer.isSome = (Lookup.first storage key).isSome := by
  obtain ⟨after, pointer, hget, hb, hv, hp⟩ := getReference_canonical ctx.trie
    (contractKey ctx.current.bytes key) accountNodes hwf.trie_canonical hwf.trie_changes_unique hnodes
  refine ⟨after, pointer, hget, hb, hv, ?_⟩
  rw [wf_storage_lookup ctx raw hwf storage hs key]
  exact hp

/-- Complete actual read contract for any boundary raw-storage list. Both
absence and exact dereferenced bytes are derived from original WF/canonicality. -/
theorem wf_canonical_read (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key : Bytes) (accountNodes : Bool) (hnodes : ctx.trie.NonzeroNodes) :
    match Lookup.first storage key with
    | none => ∃ after,
        getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes = .ok (after, none) ∧
        after.base = ctx.trie.base
    | some value => ∃ after pointer finished,
        getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes = .ok (after, some pointer) ∧
        dereference after pointer = .ok (finished, value) ∧ finished.base = ctx.trie.base := by
  rw [wf_storage_lookup ctx raw hwf storage hs key]
  exact canonical_read ctx.trie (contractKey ctx.current.bytes key) accountNodes
    hwf.trie_canonical hwf.trie_changes_unique hnodes

/-- Any actual returned pointer dereferences without failure to the raw
contract value, even when it came from a prospective/committed overlay. -/
theorem wf_canonical_dereference (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key : Bytes) (accountNodes : Bool) (hnodes : ctx.trie.NonzeroNodes)
    (after : Near.TrieOverlay.State) (pointer : ValuePointer)
    (hget : getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes = .ok (after, some pointer)) :
    ∃ value finished, Lookup.first storage key = some value ∧ (key, value) ∈ raw ∧
      dereference after pointer = .ok (finished, value) ∧ finished.base = ctx.trie.base := by
  obtain ⟨value, finished, hv, hd, hb⟩ := getReference_dereference_canonical ctx.trie
    (contractKey ctx.current.bytes key) accountNodes hwf.trie_canonical hwf.trie_changes_unique hnodes
    after pointer hget
  exact ⟨value, finished, (wf_storage_lookup ctx raw hwf storage hs key).trans hv,
    (wf_view_lookup ctx raw hwf key value).mp hv, hd, hb⟩

/-- Successful-operation presence form, useful after an actual result split. -/
theorem wf_canonical_presence (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key : Bytes) (accountNodes : Bool) (hnodes : ctx.trie.NonzeroNodes)
    (after : Near.TrieOverlay.State) (pointer : Option ValuePointer)
    (hget : getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes = .ok (after, pointer)) :
    pointer.isSome = (Lookup.first storage key).isSome := by
  rw [wf_storage_lookup ctx raw hwf storage hs key]
  exact getReference_presence_canonical ctx.trie (contractKey ctx.current.bytes key) accountNodes
    hwf.trie_canonical hwf.trie_changes_unique hnodes after pointer hget

/-- A separately split actual dereference has exactly the same raw bytes;
its success is not used as a replacement for canonical read correctness. -/
theorem wf_canonical_dereferenced_storage (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key : Bytes) (accountNodes : Bool) (hnodes : ctx.trie.NonzeroNodes)
    (after finished : Near.TrieOverlay.State) (pointer : ValuePointer) (value : Bytes)
    (hget : getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes = .ok (after, some pointer))
    (hderef : dereference after pointer = .ok (finished, value)) :
    Lookup.first storage key = some value ∧ (key, value) ∈ raw ∧ finished.base = ctx.trie.base := by
  obtain ⟨actual, result, hl, hm, hd, hb⟩ := wf_canonical_dereference ctx raw hwf storage hs key
    accountNodes hnodes after pointer hget
  rw [hderef] at hd
  cases Except.ok.inj hd
  exact ⟨hl, hm, hb⟩

end NearInterface
