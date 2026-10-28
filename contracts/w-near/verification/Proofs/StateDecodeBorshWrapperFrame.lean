import Proofs.StateDecodeBorshWrapperNative

/-! Resource and exact sequential-memory frames for accepted162 phases. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private def fields (s:Store NearState):= (s.funcs,s.modules,s.tables)
private theorem paid_fields (s:Store NearState)(op n:Nat):fields (paid s op n)=fields s:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_fields (s:Store NearState)(i:Nat)(v:Value):fields (setGlobal s i v)=fields s:=rfl
private theorem word_fields (s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):fields (storeI32 s i a m v)=fields s:=rfl
private theorem copy_fields (s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory)(n:Nat):
    fields (UnwrapStateCopyEntry.callAfter s op i out src m n)=fields s:=by
  have h:=congrArg fields (UnwrapStateCopyEffects.callAfter_resources s op i out src m n)
  exact h
private theorem child_fields (cfg:WasmConfig)(s:Store NearState)(p:StateDecodeBorsh.Layout)(q:StateDecodeVectorCopy.Layout):
    fields (StateDecodeBorsh.callAfter cfg s p q)=fields s:=by
  have h:=StateDecodeBorsh.callAfter_fields cfg s p q
  simp only[fields,h.1,h.2.1,h.2.2]
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
attribute [local irreducible] fields
attribute [local irreducible] reserved arguments decoded packedCached tagCached copyArguments copied guarded packedSaved outputArguments outputCopied accepted tagged after
attribute [local irreducible] decodedMemory firstMemory packedMemory secondMemory finalMemory packedValue tagValue

private theorem reserved_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (reserved s op p)=fields s:=by
  simp only[reserved, global_fields, paid_fields]

private theorem arguments_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (arguments s op p)=fields s:=by
  simp only[arguments, paid_fields, reserved, global_fields, paid_fields]

private theorem decoded_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (decoded cfg s p q)=fields s:=by
  unfold decoded
  rw[child_fields]
  exact arguments_fields_eq s cfg.regularOpCost p

private theorem packedCached_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (packedCached cfg s p q)=fields s:=by
  unfold packedCached
  rw[paid_fields]
  exact decoded_fields_eq cfg s p q

private theorem tagCached_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (tagCached cfg s p q)=fields s:=by
  unfold tagCached
  rw[paid_fields]
  exact packedCached_fields_eq cfg s p q

private theorem copyArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (copyArguments cfg s p q)=fields s:=by
  unfold copyArguments
  rw[paid_fields]
  exact tagCached_fields_eq cfg s p q

private theorem copied_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (copied cfg s p q)=fields s:=by
  unfold copied
  rw[copy_fields]
  exact copyArguments_fields_eq cfg s p q

private theorem guarded_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (guarded cfg s p q)=fields s:=by
  unfold guarded
  rw[paid_fields]
  exact copied_fields_eq cfg s p q

private theorem packedSaved_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (packedSaved cfg s p q)=fields s:=by
  unfold packedSaved
  rw[word_fields, paid_fields]
  exact guarded_fields_eq cfg s p q

private theorem outputArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (outputArguments cfg s p q)=fields s:=by
  unfold outputArguments
  rw[paid_fields]
  exact packedSaved_fields_eq cfg s p q

private theorem outputCopied_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (outputCopied cfg s p q)=fields s:=by
  unfold outputCopied
  rw[copy_fields]
  exact outputArguments_fields_eq cfg s p q

private theorem accepted_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (accepted cfg s p q)=fields s:=by
  unfold accepted
  rw[paid_fields]
  exact outputCopied_fields_eq cfg s p q

private theorem tagged_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (tagged cfg s p q)=fields s:=by
  unfold tagged
  rw[word_fields, paid_fields]
  exact accepted_fields_eq cfg s p q

private theorem after_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (after cfg s p q)=fields s:=by
  unfold after
  rw[global_fields, paid_fields]
  exact tagged_fields_eq cfg s p q

theorem reserved_fields (s:Store NearState)(op:Nat)(p:Layout):
    (reserved s op p).funcs=s.funcs ∧(reserved s op p).modules=s.modules ∧(reserved s op p).tables=s.tables:=by
  have h:=reserved_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem arguments_fields (s:Store NearState)(op:Nat)(p:Layout):
    (arguments s op p).funcs=s.funcs ∧(arguments s op p).modules=s.modules ∧(arguments s op p).tables=s.tables:=by
  have h:=arguments_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem decoded_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (decoded cfg s p q).funcs=s.funcs ∧(decoded cfg s p q).modules=s.modules ∧(decoded cfg s p q).tables=s.tables:=by
  have h:=decoded_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem packedCached_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedCached cfg s p q).funcs=s.funcs ∧(packedCached cfg s p q).modules=s.modules ∧(packedCached cfg s p q).tables=s.tables:=by
  have h:=packedCached_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem tagCached_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagCached cfg s p q).funcs=s.funcs ∧(tagCached cfg s p q).modules=s.modules ∧(tagCached cfg s p q).tables=s.tables:=by
  have h:=tagCached_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem copyArguments_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (copyArguments cfg s p q).funcs=s.funcs ∧(copyArguments cfg s p q).modules=s.modules ∧(copyArguments cfg s p q).tables=s.tables:=by
  have h:=copyArguments_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem copied_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (copied cfg s p q).funcs=s.funcs ∧(copied cfg s p q).modules=s.modules ∧(copied cfg s p q).tables=s.tables:=by
  have h:=copied_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem guarded_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (guarded cfg s p q).funcs=s.funcs ∧(guarded cfg s p q).modules=s.modules ∧(guarded cfg s p q).tables=s.tables:=by
  have h:=guarded_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem packedSaved_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedSaved cfg s p q).funcs=s.funcs ∧(packedSaved cfg s p q).modules=s.modules ∧(packedSaved cfg s p q).tables=s.tables:=by
  have h:=packedSaved_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem outputArguments_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (outputArguments cfg s p q).funcs=s.funcs ∧(outputArguments cfg s p q).modules=s.modules ∧(outputArguments cfg s p q).tables=s.tables:=by
  have h:=outputArguments_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem outputCopied_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (outputCopied cfg s p q).funcs=s.funcs ∧(outputCopied cfg s p q).modules=s.modules ∧(outputCopied cfg s p q).tables=s.tables:=by
  have h:=outputCopied_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem accepted_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (accepted cfg s p q).funcs=s.funcs ∧(accepted cfg s p q).modules=s.modules ∧(accepted cfg s p q).tables=s.tables:=by
  have h:=accepted_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem tagged_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagged cfg s p q).funcs=s.funcs ∧(tagged cfg s p q).modules=s.modules ∧(tagged cfg s p q).tables=s.tables:=by
  have h:=tagged_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem after_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (after cfg s p q).funcs=s.funcs ∧(after cfg s p q).modules=s.modules ∧(after cfg s p q).tables=s.tables:=by
  have h:=after_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem arguments_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (arguments s op p).mems[p.memoryIndex]?=some p.memory:=by
  simp only[arguments,paid_mems,reserved,global_mems,hm]

theorem decoded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (decoded cfg s p q).mems[p.memoryIndex]?=some (decodedMemory p q):=by
  unfold decoded
  simpa only[decodedMemory] using StateDecodeBorsh.callAfter_memory cfg (arguments s cfg.regularOpCost p) p.toBorsh q hn.child hd (arguments_memory s cfg.regularOpCost p hm)

theorem packedCached_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (packedCached cfg s p q).mems[p.memoryIndex]?=some (decodedMemory p q):=by
  rw[packedCached,paid_mems]
  exact decoded_memory cfg s p q hn hd hm

theorem tagCached_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (tagCached cfg s p q).mems[p.memoryIndex]?=some (decodedMemory p q):=by
  rw[tagCached,paid_mems]
  exact packedCached_memory cfg s p q hn hd hm

theorem copyArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (copyArguments cfg s p q).mems[p.memoryIndex]?=some (decodedMemory p q):=by
  rw[copyArguments,paid_mems]
  exact tagCached_memory cfg s p q hn hd hm

theorem copied_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (copied cfg s p q).mems[p.memoryIndex]?=some (firstMemory p q):=by
  have spec:=decodedMemory_spec p q hn hd
  have width:(decodedMemory p q).byteSize≤2^32:=by rw[spec.2.1];exact hn.child.prefixNative.child.memoryWidth
  unfold copied firstMemory
  exact UnwrapStateCopyEffects.callAfter_memory _ _ _ _ _ _ _ (copyArguments_memory cfg s p q hn hd hm) spec.1 width (first_copy_bounds p q hn hd).2 (first_copy_bounds p q hn hd).1

theorem guarded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (guarded cfg s p q).mems[p.memoryIndex]?=some (firstMemory p q):=by
  rw[guarded,paid_mems];exact copied_memory cfg s p q hn hd hm

theorem packedSaved_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (packedSaved cfg s p q).mems[p.memoryIndex]?=some (packedMemory p q):=by
  unfold packedSaved packedMemory
  apply storeI32_memory
  rw[paid_mems];exact guarded_memory cfg s p q hn hd hm

theorem outputArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (outputArguments cfg s p q).mems[p.memoryIndex]?=some (packedMemory p q):=by
  rw[outputArguments,paid_mems];exact packedSaved_memory cfg s p q hn hd hm

theorem outputCopied_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (outputCopied cfg s p q).mems[p.memoryIndex]?=some (secondMemory p q):=by
  have spec:=packedMemory_spec p q hn hd
  have width:(packedMemory p q).byteSize≤2^32:=by rw[spec.2.1];exact hn.child.prefixNative.child.memoryWidth
  unfold outputCopied secondMemory
  exact UnwrapStateCopyEffects.callAfter_memory _ _ _ _ _ _ _ (outputArguments_memory cfg s p q hn hd hm) spec.1 width (second_copy_bounds p q hn hd).2 (second_copy_bounds p q hn hd).1

theorem accepted_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (accepted cfg s p q).mems[p.memoryIndex]?=some (secondMemory p q):=by
  rw[accepted,paid_mems];exact outputCopied_memory cfg s p q hn hd hm

theorem tagged_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (tagged cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  unfold tagged finalMemory
  apply storeI32_memory
  rw[paid_mems];exact accepted_memory cfg s p q hn hd hm

theorem after_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (after cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  rw[after,global_mems,paid_mems];exact tagged_memory cfg s p q hn hd hm

private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem word_globals(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl
private theorem copy_globals(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory)(n:Nat):
    (UnwrapStateCopyEntry.callAfter s op i out src m n).globals=s.globals:=by
  have h:=congrArg (fun t:Store NearState=>t.globals) (UnwrapStateCopyEffects.callAfter_resources s op i out src m n)
  exact h

theorem reserved_global(s:Store NearState)(op:Nat)(p:Layout)(hg:s.globals[p.globalIndex]?=some p.global162):
    (reserved s op p).globals[p.globalIndex]?=some {p.global162 with value:=.i32 (scratch p)}:=by
  simp only[reserved,setGlobal,paid_globals]
  simp[Array.getElem?_modify,hg]

theorem arguments_globals(s:Store NearState)(op:Nat)(p:Layout):
    (arguments s op p).globals=(reserved s op p).globals:=by rw[arguments,paid_globals]

theorem arguments_global(s:Store NearState)(op:Nat)(p:Layout)(hn:Native p)(hg:s.globals[p.globalIndex]?=some p.global162):
    (arguments s op p).globals[p.globalIndex]?=some p.global425:=by
  rw[arguments_globals,hn.childGlobal];exact reserved_global s op p hg

theorem decoded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (decoded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  have g:=arguments_global s cfg.regularOpCost p hn hg
  have v:p.global425.value=.i32 p.sp425:=by rw[hn.childGlobal,hn.childSP]
  unfold decoded
  exact (StateDecodeBorsh.callAfter_globals cfg _ _ q hn.child hd g v).trans (arguments_globals s cfg.regularOpCost p)

theorem packedCached_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (packedCached cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[packedCached,paid_globals];exact decoded_globals cfg s p q hn hd hg

theorem tagCached_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (tagCached cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[tagCached,paid_globals];exact packedCached_globals cfg s p q hn hd hg

theorem copyArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (copyArguments cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[copyArguments,paid_globals];exact tagCached_globals cfg s p q hn hd hg

theorem copied_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (copied cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[copied,copy_globals];exact copyArguments_globals cfg s p q hn hd hg

theorem guarded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (guarded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[guarded,paid_globals];exact copied_globals cfg s p q hn hd hg

theorem packedSaved_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (packedSaved cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[packedSaved,word_globals,paid_globals];exact guarded_globals cfg s p q hn hd hg

theorem outputArguments_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (outputArguments cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[outputArguments,paid_globals];exact packedSaved_globals cfg s p q hn hd hg

theorem outputCopied_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (outputCopied cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[outputCopied,copy_globals];exact outputArguments_globals cfg s p q hn hd hg

theorem accepted_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (accepted cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[accepted,paid_globals];exact outputCopied_globals cfg s p q hn hd hg

theorem tagged_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162):
    (tagged cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  rw[tagged,word_globals,paid_globals];exact accepted_globals cfg s p q hn hd hg

theorem after_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hg:s.globals[p.globalIndex]?=some p.global162)
    (hv:p.global162.value=.i32 p.sp162):
    (after cfg s p q).globals=s.globals:=by
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global162 hg
  simp only[after,setGlobal,paid_globals,tagged_globals cfg s p q hn hd hg,reserved,paid_globals]
  simpa only[setGlobal,hv] using restore

private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_reset(seed current host:NearState):view seed (view current host)=view seed host:=rfl
private theorem view_rebase(seed current host:NearState)(h:view current host=current):view seed host=view seed current:=by
  have r:=congrArg (view seed) h
  simpa only[view_reset] using r
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_global(seed:NearState)(s:Store NearState)(i:Nat)(v:Value):view seed (setGlobal s i v).host=view seed s.host:=rfl
private theorem view_word(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_copy(seed:NearState)(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory)(n:Nat):
    view seed (UnwrapStateCopyEntry.callAfter s op i out src m n).host=view seed s.host:=by
  exact view_rebase seed s.host _ (UnwrapStateCopyEffects.callAfter_host_frame s op i out src m n)
private theorem view_child(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:StateDecodeBorsh.Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (StateDecodeBorsh.callAfter cfg s p q).host=view seed s.host:=by
  exact view_rebase seed s.host _ (StateDecodeBorsh.callAfter_functional_host cfg s p q)
attribute [local irreducible] view

private theorem view_reserved(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (reserved s op p).host=view seed s.host:=by
  rw[reserved,view_global,view_paid]

private theorem view_arguments(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (arguments s op p).host=view seed s.host:=by
  rw[arguments,view_paid,view_reserved]

private theorem view_decoded(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (decoded cfg s p q).host=view seed s.host:=by
  rw[decoded,view_child];exact view_arguments seed s cfg.regularOpCost p

private theorem view_packedCached(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (packedCached cfg s p q).host=view seed s.host:=by
  rw[packedCached,view_paid];exact view_decoded seed cfg s p q

private theorem view_tagCached(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (tagCached cfg s p q).host=view seed s.host:=by
  rw[tagCached,view_paid];exact view_packedCached seed cfg s p q

private theorem view_copyArguments(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (copyArguments cfg s p q).host=view seed s.host:=by
  rw[copyArguments,view_paid];exact view_tagCached seed cfg s p q

private theorem view_copied(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (copied cfg s p q).host=view seed s.host:=by
  rw[copied,view_copy];exact view_copyArguments seed cfg s p q

private theorem view_guarded(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (guarded cfg s p q).host=view seed s.host:=by
  rw[guarded,view_paid];exact view_copied seed cfg s p q

private theorem view_packedSaved(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (packedSaved cfg s p q).host=view seed s.host:=by
  rw[packedSaved,view_word,view_paid];exact view_guarded seed cfg s p q

private theorem view_outputArguments(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (outputArguments cfg s p q).host=view seed s.host:=by
  rw[outputArguments,view_paid];exact view_packedSaved seed cfg s p q

private theorem view_outputCopied(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (outputCopied cfg s p q).host=view seed s.host:=by
  rw[outputCopied,view_copy];exact view_outputArguments seed cfg s p q

private theorem view_accepted(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (accepted cfg s p q).host=view seed s.host:=by
  rw[accepted,view_paid];exact view_outputCopied seed cfg s p q

private theorem view_tagged(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (tagged cfg s p q).host=view seed s.host:=by
  rw[tagged,view_word,view_paid];exact view_accepted seed cfg s p q

private theorem view_after(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (after cfg s p q).host=view seed s.host:=by
  rw[after,view_global,view_paid];exact view_tagged seed cfg s p q

theorem decoded_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(decoded cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_decoded s.host cfg s p q
  simpa only[view] using h

theorem copied_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(copied cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_copied s.host cfg s p q
  simpa only[view] using h

theorem outputCopied_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(outputCopied cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_outputCopied s.host cfg s p q
  simpa only[view] using h

theorem after_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(after cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_after s.host cfg s p q
  simpa only[view] using h
end WNear.Proofs.StateDecodeBorshWrapper
