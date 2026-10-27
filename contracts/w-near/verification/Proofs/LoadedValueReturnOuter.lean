import Proofs.ValueReturnOuterState
import Proofs.LoadedValueReturnLookup

/-! The outer method's complete code certificate follows from actual loading.
Only module/resource indices and the two selected table indices remain layout
conditions; no individual function descriptor or execution result is assumed. -/
namespace WNear.Proofs.LoadedValueReturnOuter
open Wasm Wasm.Near MeteredLogic
open ValueReturnOuterBody

/-- The actual loaded function descriptors, host, and both dispatch entries. -/
theorem installed_code (cfg : RuntimeConfig) (original : NearState)
    (s : Store NearState) (p : Layout)
    (hload : LoadedValueReturnTable.Installed cfg original s p.mi)
    (htableIndex : p.mi.tableAddrs[0]? = some p.tableAddress)
    (htable : s.tables[p.tableAddress]? = some p.table)
    (hlookup : p.lookupElement = 116) (hreturn : p.returnElement = 58)
    (hmemory : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hglobal : p.mi.globalAddrs[0]? = some p.globalIndex) :
    Code s p 0 cfg.fees.numExtraBytesRecord := by
  have hcode := LoadedValueReturnTable.installed_code cfg original s p.mi hload
  have lookup := LoadedCallees.functions cfg original s p.mi hcode 517
    WNear.Binary.ValueReturnThreadLocal.lookupFunction WNear.Binary.ValueReturnThreadLocal.lookupSignature
    WNear.Binary.ValueReturnThreadLocal.lookup_function WNear.Binary.ValueReturnThreadLocal.lookup_signature
  have helper := LoadedCallees.functions cfg original s p.mi hcode 420
    WNear.Binary.ValueReturnThreadLocal.function WNear.Binary.ValueReturnThreadLocal.signature
    WNear.Binary.ValueReturnThreadLocal.module_function WNear.Binary.ValueReturnThreadLocal.module_signature
  have acquire := LoadedCallees.functions cfg original s p.mi hcode 381
    WNear.Binary.ValueReturnAcquire.acquireFunction WNear.Binary.ValueReturnAcquire.acquireSignature
    WNear.Binary.ValueReturnAcquire.acquire_function WNear.Binary.ValueReturnAcquire.acquire_signature
  have increment := LoadedCallees.functions cfg original s p.mi hcode 446
    WNear.Binary.ValueReturnAcquire.incrementFunction WNear.Binary.ValueReturnAcquire.incrementSignature
    WNear.Binary.ValueReturnAcquire.increment_function WNear.Binary.ValueReturnAcquire.increment_signature
  have nonnull := LoadedCallees.functions cfg original s p.mi hcode 382
    WNear.Binary.ValueReturnBorrow.nonnullFunction WNear.Binary.ValueReturnBorrow.nonnullSignature
    WNear.Binary.ValueReturnBorrow.nonnull_function WNear.Binary.ValueReturnBorrow.nonnull_signature
  have release := LoadedCallees.functions cfg original s p.mi hcode 383
    WNear.Binary.ValueReturnBorrow.releaseFunction WNear.Binary.ValueReturnBorrow.voidSignature
    WNear.Binary.ValueReturnBorrow.release_function WNear.Binary.ValueReturnBorrow.void_signature
  have swap := LoadedCallees.functions cfg original s p.mi hcode 624
    WNear.Binary.ValueReturnBorrow.swapFunction WNear.Binary.ValueReturnBorrow.nonnullSignature
    WNear.Binary.ValueReturnBorrow.swap_function WNear.Binary.ValueReturnBorrow.nonnull_signature
  have check := LoadedCallees.functions cfg original s p.mi hcode 385
    WNear.Binary.ValueReturnBorrow.checkFunction WNear.Binary.ValueReturnBorrow.voidSignature
    WNear.Binary.ValueReturnBorrow.check_function WNear.Binary.ValueReturnBorrow.void_signature
  have returned := LoadedCallees.functions cfg original s p.mi hcode 212
    WNear.Binary.ValueReturnLeaf.function WNear.Binary.ValueReturnLeaf.signature
    WNear.Binary.ValueReturnLeaf.module_function WNear.Binary.ValueReturnLeaf.module_signature
  have host := LoadedValueReturn.host cfg original s p.mi hcode
  obtain ⟨address, table, ha, ht, h116, h58⟩ :=
    LoadedValueReturnLookup.installed_lookup_pair cfg original s p.mi hload
  have ha' : address = p.tableAddress := Option.some.inj (ha.symm.trans htableIndex)
  subst address
  have ht' : table = p.table := Option.some.inj (ht.symm.trans htable)
  subst table
  have hlookupType : p.mi.types[1]? = some WNear.Binary.ValueReturnThreadLocal.lookupSignature := by
    rw [LoadedValueReturnDispatch.types cfg original s p.mi hcode]
    exact WNear.Binary.ValueReturnThreadLocal.lookup_signature
  have hreturnType : p.mi.types[4]? = some WNear.Binary.ValueReturnLeaf.signature := by
    rw [LoadedValueReturnDispatch.types cfg original s p.mi hcode]
    exact WNear.Binary.ValueReturnLeaf.module_signature
  exact {
    module := lookup.2.2
    tableIndex := htableIndex
    table := htable
    lookupElement := by rw [hlookup]; exact h116
    lookupType := hlookupType
    lookupFunction := lookup.2.1
    helperIndex := helper.1
    helperFunction := helper.2.1
    acquireLinks := ⟨lookup.2.2, ⟨672, swap.1, swap.2.1⟩, ⟨494, increment.1, increment.2.1⟩⟩
    acquireIndex := acquire.1
    acquireFunction := acquire.2.1
    nonnullIndex := nonnull.1
    nonnullFunction := nonnull.2.1
    releaseIndex := release.1
    releaseFunction := release.2.1
    swapIndex := swap.1
    swapFunction := swap.2.1
    checkIndex := check.1
    checkFunction := check.2.1
    returnElement := by rw [hreturn]; exact h58
    returnType := hreturnType
    returnFunction := returned.2.1
    hostIndex := host.1
    hostFunction := host.2
    memoryIndex := hmemory
    globalIndex := hglobal }

/-- Loading supplies the actual shared table; callers need not supply its
address or descriptor to construct an outer code certificate. -/
theorem installed_code_exists (cfg : RuntimeConfig) (original : NearState)
    (s : Store NearState) (p : Layout)
    (hload : LoadedValueReturnTable.Installed cfg original s p.mi)
    (hlookup : p.lookupElement = 116) (hreturn : p.returnElement = 58)
    (hmemory : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hglobal : p.mi.globalAddrs[0]? = some p.globalIndex) :
    ∃ address table, Code s {p with tableAddress := address, table := table}
      0 cfg.fees.numExtraBytesRecord := by
  obtain ⟨address, table, ha, ht, _, _⟩ :=
    LoadedValueReturnLookup.installed_lookup_pair cfg original s p.mi hload
  exact ⟨address, table, installed_code cfg original s
    {p with tableAddress := address, table := table} hload ha ht hlookup hreturn hmemory hglobal⟩

end WNear.Proofs.LoadedValueReturnOuter
