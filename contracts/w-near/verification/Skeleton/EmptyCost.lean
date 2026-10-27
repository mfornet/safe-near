import Skeleton.EmptyStorage

/-!
# Symbolic storage cost for the walking method on an empty base

The ordered ABI reads pay for one key byte from memory and the input from
register zero. No measured execution or post-state cost is used.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open MeteredHosts MeteredHosts.StorageMetered

/-- The original external cost table and input length determine prebilling. -/
def emptyStorageCost (cfg : RuntimeConfig) (length : Nat) : Nat :=
  let cost := cfg.wasm.extCosts.cost
  cost "base" + cost "storage_write_base" + cost "read_memory_base" +
    cost "read_memory_byte" + cost "read_register_base" + cost "read_register_byte" * length +
    cost "storage_write_key_byte" + cost "storage_write_value_byte" * length

/-- The successful validation plan is exactly eight ordered external charges. -/
theorem emptyPreCharges_eq (ctx : NearInterface.Context) (raw : Storage)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    emptyPreCharges ctx raw = [.ext "base", .ext "storage_write_base",
      .ext "read_memory_base", .ext "read_memory_byte" 1,
      .ext "read_register_base", .ext "read_register_byte" ctx.args.length,
      .ext "storage_write_key_byte" 1, .ext "storage_write_value_byte" ctx.args.length] := by
  have hk : getMemOrReg (emptyBefore ctx raw) 0 1 = some "k".toUTF8.toList :=
    emptyPaid_key ctx raw hpages
  have hb : "k".toUTF8.toList = [107] := by decide +kernel
  rw [hb] at hk
  have hr := storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) raw
  change (emptyBefore ctx raw).host.registers 0 = some ctx.args at hr
  have hv : getMemOrReg (emptyBefore ctx raw) 0 u64Max = some ctx.args := by
    simpa only [getMemOrReg, ↓reduceIte, UInt64.toNat_zero] using hr
  have hc := storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw
  have hkl : (emptyBefore ctx raw).host.config.maxStorageKeyLen =
      some ctx.protocol.wasm.limits.maxLengthStorageKey := congrArg (·.maxStorageKeyLen) hc
  have hvl : (emptyBefore ctx raw).host.config.maxStorageValueLen =
      some ctx.protocol.wasm.limits.maxLengthStorageValue := congrArg (·.maxStorageValueLen) hc
  have ht := storageInput_accounting ctx.protocol (Near.Boundary.toVMContext ctx) raw
  change (emptyBefore ctx raw).host.storageAccounting = some ctx.trie at ht
  have hp : storageMutationPlan? "storage_write" (emptyBefore ctx raw) (args 1 0 u64Max 0) =
      some { charges := [.ext "base", .ext "storage_write_base", .ext "read_memory_base",
        .ext "read_memory_byte" 1, .ext "read_register_base", .ext "read_register_byte" ctx.args.length,
        .ext "storage_write_key_byte" 1, .ext "storage_write_value_byte" ctx.args.length] } := by
    simp [storageMutationPlan?, args, argU64, hk, hv, hkl, hvl, Nat.not_lt.mpr hkey,
      Nat.not_lt.mpr hvalue, readSpan, hr, show (1 : UInt64) ≠ u64Max by decide +kernel,
      storageValueCharges, ht]
  simp only [emptyPreCharges, chargesBefore, hp]

/-- The storage cost is symbolic in the original protocol and input length. -/
theorem emptyCost_eq (ctx : NearInterface.Context) (raw : Storage)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    emptyCost ctx raw = emptyStorageCost ctx.protocol ctx.args.length := by
  have hext := storageInput_extCosts ctx.protocol (Near.Boundary.toVMContext ctx) raw
  rw [emptyCost, emptyPreCharges_eq ctx raw hpages hkey hvalue]
  change burnSum (emptyBefore ctx raw).host.extCosts _ = _
  rw [hext]
  simp [burnSum, burnCost, VMContext.toNearState, emptyStorageCost, Nat.add_assoc]

end WNear.Skeleton
