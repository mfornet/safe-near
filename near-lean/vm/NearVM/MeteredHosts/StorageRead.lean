import NearVM.MeteredHosts.StorageMetered

/-! Raw storage reads and their actual lookup/proof/dereference phase. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open StorageMetered
open _root_.Near.TrieOverlay
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

def args (keyLen keyPtr register : UInt64) : List Value := [.i64 keyLen, .i64 keyPtr, .i64 register]
def written (before : HostStore NearState) (register : UInt64) (value : List UInt8) : HostStore NearState :=
  if register = u64Max then before else {before with host := before.host.setRegister register.toNat value}

theorem raw_hit (before : HostStore NearState) (keyLen keyPtr register : UInt64) (key value : List UInt8)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hs : before.host.storage key = some value)
    (hr : register = u64Max ∨ withinLimit before.host.config.maxRegisterLen value.length = true) :
    storageReadFn.invoke before (args keyLen keyPtr register) = .Return [.i64 1] (written before register value) := by
  simp only [storageReadFn, args, hk, checkDataLimit, hl, ↓reduceIte, hs]
  rcases hr with rfl | hreg
  · simp only [writeRegisterResult, checkedSetRegister?, written, ↓reduceIte]
  · by_cases hd : register = u64Max
    · simp only [writeRegisterResult, checkedSetRegister?, written, hd, ↓reduceIte]
    · simp only [writeRegisterResult, checkedSetRegister?, written, hd, ↓reduceIte, hreg]

theorem raw_miss (before : HostStore NearState) (keyLen keyPtr register : UInt64) (key : List UInt8)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hs : before.host.storage key = none) :
    storageReadFn.invoke before (args keyLen keyPtr register) = .Return [.i64 0] before := by
  simp only [storageReadFn, args, hk, checkDataLimit, hl, ↓reduceIte, hs]

local macro "unfold_storage_aux" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearVM.Metered 0) "Wasm") "Near") "prepareStorageCallAux"
  `(tactic| unfold $(Lean.mkIdent name))

/-- Misses bill lookup nodes and check its proof before returning unchanged raw storage. -/
theorem prepare_miss (before : HostStore NearState) (keyLen keyPtr register : UInt64) (key : List UInt8)
    (initial looked : State) (paid : NearState)
    (ha : before.host.storageAccounting = some initial)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hg : getReference initial (contractKey before.host.context.currentAccountId key)
      before.host.storageReadsFromTrie = .ok (looked, none))
    (hs : before.host.storage key = none)
    (hc : applyCharges (accounted before looked).host (trieCharges initial looked) = (paid, none))
    (hp : recordedStorageError paid looked = none) :
    prepareStorageCall "storage_read" before (args keyLen keyPtr register) = (prepared before paid looked, none) := by
  have hacc : paid.storageAccounting = some looked := by
    have f := congrArg (fun ns : NearState => ns.storageAccounting)
      (applyCharges_frame (accounted before looked).host (trieCharges initial looked)
        (trieCharges_burnsOnly initial looked))
    change (applyCharges (accounted before looked).host (trieCharges initial looked)).1.storageAccounting = some looked at f
    rw [hc] at f
    exact f
  simp only [accounted, trieCharges] at hc
  simp only [recordedStorageError] at hp
  unfold prepareStorageCall
  unfold_storage_aux
  simp only [Id.run, pure, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_read" = true by decide,
    ↓reduceIte, ha, hk]
  cases hlimit : before.host.config.maxStorageKeyLen with
  | none => simp [hg, hs, hc, recordedStorageError, hp, prepared, hacc]
  | some limit =>
    simp only [Nat.not_lt_of_ge (hl limit hlimit), ↓reduceIte]
    simp [hg, hs, hc, recordedStorageError, hp, prepared, hacc]

/-- Hits bill proof lookup first, then the referenced value bytes, before actual dereference. -/
theorem prepare_hit (before : HostStore NearState) (keyLen keyPtr register : UInt64) (key value : List UInt8)
    (initial looked fetched : State) (pointer : ValuePointer) (nodePaid valuePaid : NearState)
    (ha : before.host.storageAccounting = some initial)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hg : getReference initial (contractKey before.host.context.currentAccountId key)
      before.host.storageReadsFromTrie = .ok (looked, some pointer))
    (hs : before.host.storage key = some value)
    (hc : applyCharges (accounted before looked).host (trieCharges initial looked) = (nodePaid, none))
    (hp : recordedStorageError nodePaid looked = none)
    (hv : applyCharges nodePaid (storageReadValueCharges pointer.reference.2.length) = (valuePaid, none))
    (hd : dereference looked pointer = .ok (fetched, value)) :
    prepareStorageCall "storage_read" before (args keyLen keyPtr register) = (prepared before valuePaid fetched, none) := by
  simp only [accounted, trieCharges] at hc
  simp only [recordedStorageError] at hp
  unfold prepareStorageCall
  unfold_storage_aux
  simp only [Id.run, pure, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_read" = true by decide,
    ↓reduceIte, ha, hk]
  cases hlimit : before.host.config.maxStorageKeyLen with
  | none => simp [hg, hs, hc, recordedStorageError, hp, hv, hd, prepared]
  | some limit =>
    simp only [Nat.not_lt_of_ge (hl limit hlimit), ↓reduceIte]
    simp [hg, hs, hc, recordedStorageError, hp, hv, hd, prepared]

end Wasm.Near.MeteredHosts.StorageRead
