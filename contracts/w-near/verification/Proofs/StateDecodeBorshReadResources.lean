import Proofs.StateDecodeBorshReadFrame
import Proofs.StateDecodeBorshReadMemoryNative

/-! Selected-memory and exact global-array frames for every161 stage. The
prepared162 facts are derived from original inputs. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem charge_mems(s:Store NearState)(op:Nat):(chargedStore s op).mems=s.mems:=rfl
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem word_globals(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl
private theorem charge_globals(s:Store NearState)(op:Nat):(chargedStore s op).globals=s.globals:=rfl
private theorem copy_globals(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory)(n:Nat):
    (UnwrapStateCopyEntry.callAfter s op i out src m n).globals=s.globals:=by
  have h:=congrArg (fun t:Store NearState=>t.globals) (UnwrapStateCopyEffects.callAfter_resources s op i out src m n)
  exact h
attribute [local irreducible] readI32 readI64 writeI32 writeI64 setupMemory highSetupMemory
attribute [local irreducible] StateDecodeBorshWrapper.finalMemory
attribute [local irreducible] reserved highSaved sliceSaved wrapperArguments wrapped packedCached tagCached firstCopyArguments firstCopied firstDropped guarded upperSaved acceptedCopyArguments acceptedCopied acceptedDropped exhausted resultCopyArguments resultCopied resultDropped tagged branched after wrappedMemory scratchMemory upperMemory acceptedMemory resultMemory finalMemory

theorem reserved_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (reserved s op p).mems[p.memoryIndex]?=some (p.memory):=by
  rw[reserved,global_mems,paid_mems]
  exact hm

theorem highSaved_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (highSaved s op p).mems[p.memoryIndex]?=some (highSetupMemory p):=by
  unfold highSaved highSetupMemory
  apply storeI32_memory
  rw[paid_mems];exact reserved_memory s op p hm

theorem sliceSaved_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (sliceSaved s op p).mems[p.memoryIndex]?=some (setupMemory p):=by
  unfold sliceSaved setupMemory
  apply storeI32_memory
  rw[paid_mems];exact highSaved_memory s op p hm

theorem wrapperArguments_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wrapperArguments s op p).mems[p.memoryIndex]?=some (setupMemory p):=by
  rw[wrapperArguments,paid_mems]
  exact sliceSaved_memory s op p hm

theorem wrapped_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (wrapped cfg s p q).mems[p.memoryIndex]?=some (wrappedMemory p q):=by
  unfold wrapped wrappedMemory
  exact StateDecodeBorshWrapper.callAfter_memory cfg _ (actualWrapper p) (actualAllocation p q) (wrapper_native p hn) (accepted_domain p q hn hd) (wrapperArguments_memory s cfg.regularOpCost p hm)

theorem packedCached_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (packedCached cfg s p q).mems[p.memoryIndex]?=some (wrappedMemory p q):=by
  rw[packedCached,paid_mems]
  exact wrapped_memory cfg s p q hn hd hm

theorem tagCached_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (tagCached cfg s p q).mems[p.memoryIndex]?=some (wrappedMemory p q):=by
  rw[tagCached,paid_mems]
  exact packedCached_memory cfg s p q hn hd hm

theorem firstCopyArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (firstCopyArguments cfg s p q).mems[p.memoryIndex]?=some (wrappedMemory p q):=by
  rw[firstCopyArguments,paid_mems]
  exact tagCached_memory cfg s p q hn hd hm

theorem firstCopied_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (firstCopied cfg s p q).mems[p.memoryIndex]?=some (scratchMemory p q):=by
  have spec:=wrappedMemory_spec p q hn hd
  have width:(wrappedMemory p q).byteSize≤2^32:=by rw[spec.2.1];exact hn.width
  unfold firstCopied scratchMemory
  exact UnwrapStateCopyEffects.callAfter_memory _ _ _ _ _ _ _ (firstCopyArguments_memory cfg s p q hn hd hm) spec.1 width (first_copy_bounds p q hn hd).2 (first_copy_bounds p q hn hd).1

theorem firstDropped_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (firstDropped cfg s p q).mems[p.memoryIndex]?=some (scratchMemory p q):=by
  rw[firstDropped,paid_mems]
  exact firstCopied_memory cfg s p q hn hd hm

theorem guarded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (guarded cfg s p q).mems[p.memoryIndex]?=some (scratchMemory p q):=by
  rw[guarded,paid_mems]
  exact firstDropped_memory cfg s p q hn hd hm

theorem upperSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (upperSaved cfg s p q).mems[p.memoryIndex]?=some (upperMemory p q):=by
  unfold upperSaved upperMemory
  apply storeI32_memory
  rw[paid_mems];exact guarded_memory cfg s p q hn hd hm

theorem acceptedCopyArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (acceptedCopyArguments cfg s p q).mems[p.memoryIndex]?=some (upperMemory p q):=by
  rw[acceptedCopyArguments,paid_mems]
  exact upperSaved_memory cfg s p q hn hd hm

theorem acceptedCopied_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (acceptedCopied cfg s p q).mems[p.memoryIndex]?=some (acceptedMemory p q):=by
  have spec:=upperMemory_spec p q hn hd
  have width:(upperMemory p q).byteSize≤2^32:=by rw[spec.2.1];exact hn.width
  unfold acceptedCopied acceptedMemory
  exact UnwrapStateCopyEffects.callAfter_memory _ _ _ _ _ _ _ (acceptedCopyArguments_memory cfg s p q hn hd hm) spec.1 width (accepted_copy_bounds p q hn hd).2 (accepted_copy_bounds p q hn hd).1

theorem acceptedDropped_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (acceptedDropped cfg s p q).mems[p.memoryIndex]?=some (acceptedMemory p q):=by
  rw[acceptedDropped,paid_mems]
  exact acceptedCopied_memory cfg s p q hn hd hm

theorem exhausted_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (exhausted cfg s p q).mems[p.memoryIndex]?=some (acceptedMemory p q):=by
  rw[exhausted,paid_mems]
  exact acceptedDropped_memory cfg s p q hn hd hm

theorem resultCopyArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (resultCopyArguments cfg s p q).mems[p.memoryIndex]?=some (acceptedMemory p q):=by
  rw[resultCopyArguments,paid_mems]
  exact exhausted_memory cfg s p q hn hd hm

theorem resultCopied_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (resultCopied cfg s p q).mems[p.memoryIndex]?=some (resultMemory p q):=by
  have spec:=acceptedMemory_spec p q hn hd
  have width:(acceptedMemory p q).byteSize≤2^32:=by rw[spec.2.1];exact hn.width
  unfold resultCopied resultMemory
  exact UnwrapStateCopyEffects.callAfter_memory _ _ _ _ _ _ _ (resultCopyArguments_memory cfg s p q hn hd hm) spec.1 width (result_copy_bounds p q hn hd).2 (result_copy_bounds p q hn hd).1

theorem resultDropped_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (resultDropped cfg s p q).mems[p.memoryIndex]?=some (resultMemory p q):=by
  rw[resultDropped,paid_mems]
  exact resultCopied_memory cfg s p q hn hd hm

theorem tagged_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (tagged cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  unfold tagged finalMemory
  apply storeI32_memory
  rw[paid_mems];exact resultDropped_memory cfg s p q hn hd hm

theorem branched_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (branched cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  rw[branched,charge_mems]
  exact tagged_memory cfg s p q hn hd hm

theorem after_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (after cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  rw[after,global_mems,paid_mems]
  exact branched_memory cfg s p q hn hd hm

theorem reserved_global(s:Store NearState)(op:Nat)(p:Layout)(hg:s.globals[p.globalIndex]?=some p.global161):
    (reserved s op p).globals[p.globalIndex]?=some {p.global161 with value:=.i32 (scratch p)}:=by
  simp only[reserved,setGlobal,paid_globals]
  simp[Array.getElem?_modify,hg]

theorem highSaved_globals(s:Store NearState)(op:Nat)(p:Layout):
    (highSaved s op p).globals=(reserved s op p).globals:=by
  rw[highSaved,word_globals,paid_globals]

theorem sliceSaved_globals(s:Store NearState)(op:Nat)(p:Layout):
    (sliceSaved s op p).globals=(reserved s op p).globals:=by
  rw[sliceSaved,word_globals,paid_globals]
  exact highSaved_globals s op p

theorem wrapperArguments_globals(s:Store NearState)(op:Nat)(p:Layout):
    (wrapperArguments s op p).globals=(reserved s op p).globals:=by
  rw[wrapperArguments,paid_globals]
  exact sliceSaved_globals s op p

theorem wrapped_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (wrapped cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  have global:(wrapperArguments s cfg.regularOpCost p).globals[p.globalIndex]?=some (actualWrapper p).global162:=by
    rw[wrapperArguments_globals]
    change (reserved s cfg.regularOpCost p).globals[p.globalIndex]?=some p.global162
    rw[hn.wrapperGlobal];exact reserved_global s cfg.regularOpCost p hg
  have value:(actualWrapper p).global162.value=.i32 (actualWrapper p).sp162:=by
    change p.global162.value=.i32 p.sp162
    rw[hn.wrapperGlobal,hn.wrapperSP]
  unfold wrapped
  exact (StateDecodeBorshWrapper.callAfter_globals cfg _ (actualWrapper p) (actualAllocation p q) (wrapper_native p hn) (accepted_domain p q hn hd) global value).trans (wrapperArguments_globals s cfg.regularOpCost p)

theorem packedCached_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (packedCached cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[packedCached,paid_globals]
  exact wrapped_globals cfg s p q hn hd hg

theorem tagCached_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (tagCached cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[tagCached,paid_globals]
  exact packedCached_globals cfg s p q hn hd hg

theorem firstCopyArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (firstCopyArguments cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[firstCopyArguments,paid_globals]
  exact tagCached_globals cfg s p q hn hd hg

theorem firstCopied_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (firstCopied cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[firstCopied,copy_globals]
  exact firstCopyArguments_globals cfg s p q hn hd hg

theorem firstDropped_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (firstDropped cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[firstDropped,paid_globals]
  exact firstCopied_globals cfg s p q hn hd hg

theorem guarded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (guarded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[guarded,paid_globals]
  exact firstDropped_globals cfg s p q hn hd hg

theorem upperSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (upperSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[upperSaved,word_globals,paid_globals]
  exact guarded_globals cfg s p q hn hd hg

theorem acceptedCopyArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (acceptedCopyArguments cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[acceptedCopyArguments,paid_globals]
  exact upperSaved_globals cfg s p q hn hd hg

theorem acceptedCopied_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (acceptedCopied cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[acceptedCopied,copy_globals]
  exact acceptedCopyArguments_globals cfg s p q hn hd hg

theorem acceptedDropped_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (acceptedDropped cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[acceptedDropped,paid_globals]
  exact acceptedCopied_globals cfg s p q hn hd hg

theorem exhausted_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (exhausted cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[exhausted,paid_globals]
  exact acceptedDropped_globals cfg s p q hn hd hg

theorem resultCopyArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (resultCopyArguments cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[resultCopyArguments,paid_globals]
  exact exhausted_globals cfg s p q hn hd hg

theorem resultCopied_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (resultCopied cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[resultCopied,copy_globals]
  exact resultCopyArguments_globals cfg s p q hn hd hg

theorem resultDropped_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (resultDropped cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[resultDropped,paid_globals]
  exact resultCopied_globals cfg s p q hn hd hg

theorem tagged_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (tagged cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[tagged,word_globals,paid_globals]
  exact resultDropped_globals cfg s p q hn hd hg

theorem branched_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161):
    (branched cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[branched,charge_globals]
  exact tagged_globals cfg s p q hn hd hg

theorem wrapperArguments_global(s:Store NearState)(op:Nat)(p:Layout)(hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global161):
    (wrapperArguments s op p).globals[p.globalIndex]?=some (actualWrapper p).global162:=by
  rw[wrapperArguments_globals]
  change (reserved s op p).globals[p.globalIndex]?=some p.global162
  rw[hn.wrapperGlobal];exact reserved_global s op p hg

theorem after_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hg:s.globals[p.globalIndex]?=some p.global161)(hv:p.global161.value=.i32 p.sp161):
    (after cfg s p q).globals=s.globals:=by
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global161 hg
  simp only[after,setGlobal,paid_globals,branched_globals cfg s p q hn hd hg,reserved,paid_globals]
  simpa only[setGlobal,hv] using restore
end WNear.Proofs.StateDecodeBorshRead
