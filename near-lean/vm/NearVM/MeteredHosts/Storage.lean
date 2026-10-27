import NearVM.Metered
import NearVM.GasCredits

/-!
# Storage-write functional core

The M2 module discards evicted values (`register_id = u64::MAX`). These
lemmas isolate its storage update from the metered wrapper's trie access,
charges and usage accounting, which remain separate obligations. The raw
host consumes no gas, so it retains the caller's entire credit reservation.
-/
namespace Wasm.Near.MeteredHosts

/-- Storage update performed by the raw host, invalidating existing iterators. -/
def written (st : HostStore NearState) (key value : List UInt8) : HostStore NearState :=
  { st with host := (st.host.setStorage key value).invalidateIterators }

/-- Exact core behavior for both a fresh key and a replacement. The memory,
registers, gas and all other host fields are retained by `written`. -/
theorem storageWrite_discard (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (hview : st.host.context.isView = false)
    (hkey : getMemOrReg st keyPtr keyLen = some key)
    (hvalue : getMemOrReg st valuePtr valueLen = some value)
    (hkeyLimit : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit st.host.config.maxStorageValueLen value.length = true) :
    storageWriteFn.invoke st [.i64 keyLen, .i64 keyPtr, .i64 valueLen, .i64 valuePtr, .i64 u64Max] =
      .Return [.i64 (if (st.host.storage key).isSome then 1 else 0)] (written st key value) := by
  simp only [storageWriteFn, disallowInView, hview, Bool.false_eq_true, ↓reduceIte,
    hkey, hvalue, checkDataLimit, hkeyLimit, hvalueLimit]
  cases hstorage : st.host.storage key <;>
    simp [checkedSetRegister?, written]

@[simp] theorem written_memory (st : HostStore NearState) (key value : List UInt8) :
    (written st key value).mem = st.mem := rfl

@[simp] theorem written_registers (st : HostStore NearState) (key value : List UInt8) :
    (written st key value).host.registers = st.host.registers := rfl

@[simp] theorem written_gas (st : HostStore NearState) (key value : List UInt8) :
    (written st key value).host.gas = st.host.gas := rfl

/-- Gas resources pass through the functional core unchanged. -/
theorem written_credits {st : HostStore NearState} (key value : List UInt8) {credits : Nat}
    (h : st.host.gas.Credits credits) : (written st key value).host.gas.Credits credits := h

@[simp] theorem written_here (st : HostStore NearState) (key value : List UInt8) :
    (written st key value).host.storage key = some value := by
  simp [written, NearState.setStorage, NearState.invalidateIterators]

/-- No unrelated storage cell changes, including absent cells. -/
theorem written_other (st : HostStore NearState) (key value other : List UInt8)
    (h : other ≠ key) : (written st key value).host.storage other = st.host.storage other := by
  simp [written, NearState.setStorage, NearState.invalidateIterators, h]

/-- Storage usage before conversion to the ABI's `u64`. -/
def writeUsage (extra : Nat) (st : HostStore NearState) (key value : List UInt8) : Nat :=
  match st.host.storage key with
  | none => st.host.context.storageUsage.toNat + key.length + value.length + extra
  | some old => st.host.context.storageUsage.toNat + value.length - old.length

/-- The usage update is exact, with the ABI's wrapping made explicit. -/
theorem storageWrite_usage (extra : Nat) (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (hkey : getMemOrReg st keyPtr keyLen = some key) :
    (updateStorageUsage extra "storage_write" st (written st key value)
      [.i64 keyLen, .i64 keyPtr, .i64 valueLen, .i64 valuePtr, .i64 u64Max]).host.context.storageUsage =
        UInt64.ofNat (writeUsage extra st key value) := by
  simp only [updateStorageUsage, argU64, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hkey, written_here, Option.map_some]
  cases h : st.host.storage key <;> simp [writeUsage, h, written, NearState.setStorage,
    NearState.invalidateIterators]

/-- The numeric usage agreed by the model follows once overflow is excluded. -/
theorem storageWrite_usage_toNat (extra : Nat) (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (hkey : getMemOrReg st keyPtr keyLen = some key)
    (hroom : writeUsage extra st key value < 2 ^ 64) :
    (updateStorageUsage extra "storage_write" st (written st key value)
      [.i64 keyLen, .i64 keyPtr, .i64 valueLen, .i64 valuePtr, .i64 u64Max]).host.context.storageUsage.toNat =
        writeUsage extra st key value := by
  rw [storageWrite_usage extra st keyLen keyPtr valueLen valuePtr key value hkey]
  exact UInt64.toNat_ofNat_of_lt' hroom

end Wasm.Near.MeteredHosts
