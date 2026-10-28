import Proofs.StateDecodeBorshPhases
import Proofs.StateDecodePrefixWrapperCallResult
import Proofs.StateDecodeScalarResult

/-! Actual425 selected memory lookups from original memory, with exact sequential snapshots. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem charge_mems(s:Store NearState)(op:Nat):(chargedStore s op).mems=s.mems:=rfl
private theorem wide_index(p:Layout)(q:StateDecodeVectorCopy.Layout):(wideLayout p q).memoryIndex=p.memoryIndex:=rfl
private theorem wide_memory(p:Layout)(q:StateDecodeVectorCopy.Layout):(wideLayout p q).memory=savedPrefixMemory p q:=rfl
private theorem narrow_index(p:Layout)(q:StateDecodeVectorCopy.Layout):(narrowLayout p q).memoryIndex=p.memoryIndex:=rfl
private theorem narrow_memory(p:Layout)(q:StateDecodeVectorCopy.Layout):(narrowLayout p q).memory=savedWideMemory p q:=rfl
attribute [local irreducible] reserved prefixArguments prefixDecoded prefixCached prefixGuarded prefixHighSaved prefixSaved wideArguments wideDecoded wideFirstSaved wideSecondSaved wideSaved wideGuarded wideCached narrowArguments narrowDecoded narrowHighSaved narrowSaved narrowGuarded vectorHighSaved vectorSaved usageCached output16 output8 output24 output32 output40 tagged branched after scratch count prefixMemory prefixPacked prefixLength prefixHighMemory savedPrefixMemory wideLayout wideMemory wideFirstMemory wideSecondMemory savedWideMemory wideHigh wideLow narrowLayout narrowMemory narrowHighMemory savedNarrowMemory vectorLength vectorHighMemory vectorPacked cachedMemory usageValue output16Memory output8Memory output24Memory output32Memory output40Memory finalMemory

theorem reserved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (reserved s cfg.regularOpCost p).mems[p.memoryIndex]?=some p.memory:=by
  rw[reserved,global_mems,paid_mems];exact hm

theorem prefixArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (prefixArguments s cfg.regularOpCost p).mems[p.memoryIndex]?=some p.memory:=by
  have h:=reserved_memory cfg s p hm
  rw[prefixArguments,paid_mems];exact h

theorem prefixDecoded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (prefixDecoded cfg s p q).mems[p.memoryIndex]?=some (prefixMemory p q):=by
  have h:=prefixArguments_memory cfg s p hm
  have called:=StateDecodePrefixWrapper.callAfter_memory cfg (prefixArguments s cfg.regularOpCost p) p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain h
  unfold prefixDecoded prefixMemory
  exact called

theorem prefixCached_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (prefixCached cfg s p q).mems[p.memoryIndex]?=some (prefixMemory p q):=by
  have h:=prefixDecoded_memory cfg s p q hn hd hm
  rw[prefixCached,paid_mems];exact h

theorem prefixGuarded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (prefixGuarded cfg s p q).mems[p.memoryIndex]?=some (prefixMemory p q):=by
  have h:=prefixCached_memory cfg s p q hn hd hm
  rw[prefixGuarded,paid_mems];exact h

theorem prefixHighSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (prefixHighSaved cfg s p q).mems[p.memoryIndex]?=some (prefixHighMemory p q):=by
  have h:=prefixGuarded_memory cfg s p q hn hd hm
  unfold prefixHighSaved prefixHighMemory
  apply storeI32_memory
  rw[paid_mems]
  exact h

theorem prefixSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (prefixSaved cfg s p q).mems[p.memoryIndex]?=some (savedPrefixMemory p q):=by
  have h:=prefixHighSaved_memory cfg s p q hn hd hm
  unfold prefixSaved savedPrefixMemory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem wideArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wideArguments cfg s p q).mems[p.memoryIndex]?=some (savedPrefixMemory p q):=by
  have h:=prefixSaved_memory cfg s p q hn hd hm
  rw[wideArguments,paid_mems];exact h

theorem wideDecoded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wideDecoded cfg s p q).mems[p.memoryIndex]?=some (wideMemory p q):=by
  have h:=wideArguments_memory cfg s p q hn hd hm
  have initial:(wideArguments cfg s p q).mems[(wideLayout p q).memoryIndex]?=some (wideLayout p q).memory:=by
    rw[wide_index,wide_memory];exact h
  have called:=StateDecodeScalar.callAfter_memory true cfg (wideArguments cfg s p q) (wideLayout p q) initial
  rw[wide_index] at called
  unfold wideDecoded wideMemory
  exact called

theorem wideFirstSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wideFirstSaved cfg s p q).mems[p.memoryIndex]?=some (wideFirstMemory p q):=by
  have h:=wideDecoded_memory cfg s p q hn hd hm
  unfold wideFirstSaved wideFirstMemory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem wideSecondSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wideSecondSaved cfg s p q).mems[p.memoryIndex]?=some (wideSecondMemory p q):=by
  have h:=wideFirstSaved_memory cfg s p q hn hd hm
  unfold wideSecondSaved wideSecondMemory
  apply storeI32_memory
  rw[paid_mems]
  exact h

theorem wideSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wideSaved cfg s p q).mems[p.memoryIndex]?=some (savedWideMemory p q):=by
  have h:=wideSecondSaved_memory cfg s p q hn hd hm
  unfold wideSaved savedWideMemory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem wideGuarded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wideGuarded cfg s p q).mems[p.memoryIndex]?=some (savedWideMemory p q):=by
  have h:=wideSaved_memory cfg s p q hn hd hm
  rw[wideGuarded,paid_mems];exact h

theorem wideCached_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wideCached cfg s p q).mems[p.memoryIndex]?=some (savedWideMemory p q):=by
  have h:=wideGuarded_memory cfg s p q hn hd hm
  rw[wideCached,paid_mems];exact h

theorem narrowArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (narrowArguments cfg s p q).mems[p.memoryIndex]?=some (savedWideMemory p q):=by
  have h:=wideCached_memory cfg s p q hn hd hm
  rw[narrowArguments,paid_mems];exact h

theorem narrowDecoded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (narrowDecoded cfg s p q).mems[p.memoryIndex]?=some (narrowMemory p q):=by
  have h:=narrowArguments_memory cfg s p q hn hd hm
  have initial:(narrowArguments cfg s p q).mems[(narrowLayout p q).memoryIndex]?=some (narrowLayout p q).memory:=by
    rw[narrow_index,narrow_memory];exact h
  have called:=StateDecodeScalar.callAfter_memory false cfg (narrowArguments cfg s p q) (narrowLayout p q) initial
  rw[narrow_index] at called
  unfold narrowDecoded narrowMemory
  exact called

theorem narrowHighSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (narrowHighSaved cfg s p q).mems[p.memoryIndex]?=some (narrowHighMemory p q):=by
  have h:=narrowDecoded_memory cfg s p q hn hd hm
  unfold narrowHighSaved narrowHighMemory
  apply storeI32_memory
  rw[paid_mems]
  exact h

theorem narrowSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (narrowSaved cfg s p q).mems[p.memoryIndex]?=some (savedNarrowMemory p q):=by
  have h:=narrowHighSaved_memory cfg s p q hn hd hm
  unfold narrowSaved savedNarrowMemory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem narrowGuarded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (narrowGuarded cfg s p q).mems[p.memoryIndex]?=some (savedNarrowMemory p q):=by
  have h:=narrowSaved_memory cfg s p q hn hd hm
  rw[narrowGuarded,paid_mems];exact h

theorem vectorHighSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (vectorHighSaved cfg s p q).mems[p.memoryIndex]?=some (vectorHighMemory p q):=by
  have h:=narrowGuarded_memory cfg s p q hn hd hm
  unfold vectorHighSaved vectorHighMemory
  apply storeI32_memory
  rw[paid_mems]
  exact h

theorem vectorSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (vectorSaved cfg s p q).mems[p.memoryIndex]?=some (cachedMemory p q):=by
  have h:=vectorHighSaved_memory cfg s p q hn hd hm
  unfold vectorSaved cachedMemory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem usageCached_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (usageCached cfg s p q).mems[p.memoryIndex]?=some (cachedMemory p q):=by
  have h:=vectorSaved_memory cfg s p q hn hd hm
  rw[usageCached,paid_mems];exact h

theorem output16_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (output16 cfg s p q).mems[p.memoryIndex]?=some (output16Memory p q):=by
  have h:=usageCached_memory cfg s p q hn hd hm
  unfold output16 output16Memory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem output8_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (output8 cfg s p q).mems[p.memoryIndex]?=some (output8Memory p q):=by
  have h:=output16_memory cfg s p q hn hd hm
  unfold output8 output8Memory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem output24_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (output24 cfg s p q).mems[p.memoryIndex]?=some (output24Memory p q):=by
  have h:=output8_memory cfg s p q hn hd hm
  unfold output24 output24Memory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem output32_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (output32 cfg s p q).mems[p.memoryIndex]?=some (output32Memory p q):=by
  have h:=output24_memory cfg s p q hn hd hm
  unfold output32 output32Memory
  apply storeI64_memory
  rw[paid_mems]
  exact h

theorem output40_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (output40 cfg s p q).mems[p.memoryIndex]?=some (output40Memory p q):=by
  have h:=output32_memory cfg s p q hn hd hm
  unfold output40 output40Memory
  apply storeI32_memory
  rw[paid_mems]
  exact h

theorem tagged_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (tagged cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  have h:=output40_memory cfg s p q hn hd hm
  unfold tagged finalMemory
  apply storeI32_memory
  rw[paid_mems]
  exact h

theorem branched_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (branched cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  have h:=tagged_memory cfg s p q hn hd hm
  rw[branched,charge_mems];exact h

theorem after_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (after cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  have h:=branched_memory cfg s p q hn hd hm
  rw[after,global_mems,paid_mems];exact h
end WNear.Proofs.StateDecodeBorsh
