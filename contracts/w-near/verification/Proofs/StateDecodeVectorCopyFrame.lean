import Proofs.StateDecodeVectorCopyCall

/-! Exact memory, code, stack-global and functional-host endpoints for374. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] vectorAfter copied after callAfter StateDecodeVector.callAfter UnwrapStateCopyEntry.callAfter
private theorem mems_paid (s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid (s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private def fields(s:Store NearState):=(s.funcs,s.modules,s.tables)
private theorem fields_paid (s:Store NearState)(op n:Nat):fields (paid s op n)=fields s:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem fields_store (s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):fields (storeI32 s i a m v)=fields s:=rfl
private theorem fields_pack (s t:Store NearState)(h:t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables):fields t=fields s:=Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem fields_vector (cfg:WasmConfig)(s:Store NearState)(p:Layout):fields (vectorAfter cfg s p)=fields s:=by
  unfold vectorAfter
  rw[fields_pack _ _ (StateDecodeVector.callAfter_fields cfg (vectorBefore s cfg.regularOpCost) p.toVector),vectorBefore,fields_paid]
private theorem copy_fields (s:Store NearState)(op i:Nat)(out source:UInt32)(m:Memory)(n:Nat):
    fields (UnwrapStateCopyEntry.callAfter s op i out source m n)=fields s:=by
  have h:=congrArg fields (UnwrapStateCopyEffects.callAfter_resources s op i out source m n)
  exact h
private theorem copy_globals (s:Store NearState)(op i:Nat)(out source:UInt32)(m:Memory)(n:Nat):
    (UnwrapStateCopyEntry.callAfter s op i out source m n).globals=s.globals:=by
  have h:=congrArg (fun t:Store NearState=>t.globals) (UnwrapStateCopyEffects.callAfter_resources s op i out source m n)
  exact h

theorem after_memory (cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p):=by
  have vm:(vectorBefore s cfg.regularOpCost).mems[p.memoryIndex]?=some p.memory:=by rw[vectorBefore,mems_paid];exact hm
  have am:(vectorAfter cfg s p).mems[p.memoryIndex]?=some (StateDecodeVector.finalMemory p.toVector):=by
    unfold vectorAfter
    exact StateDecodeVector.callAfter_memory cfg _ p.toVector hn.vector vm
  have args:(copyArguments cfg s p).mems[p.memoryIndex]?=some (StateDecodeVector.finalMemory p.toVector):=by rw[copyArguments,mems_paid];exact am
  have b:=copy_bounds p hn
  have cm:(copied cfg s p).mems[p.memoryIndex]?=some (copiedMemory p):=by
    unfold copied copiedMemory
    exact UnwrapStateCopyEffects.callAfter_memory _ cfg.regularOpCost p.memoryIndex (pointer p) p.source _ p.size.toNat args b.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2.1
  have paidMem:(paid (copied cfg s p) cfg.regularOpCost 4).mems[p.memoryIndex]?=some (copiedMemory p):=by rw[mems_paid];exact cm
  unfold after finishStore finalMemory
  exact storeI32_memory _ p.memoryIndex (p.outVector.toNat+8) (copiedMemory p) p.size paidMem

theorem after_fields (cfg:WasmConfig)(s:Store NearState)(p:Layout):
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧ (after cfg s p).tables=s.tables:=by
  have h:fields (after cfg s p)=fields s:=by
    rw[after,finishStore,fields_store,fields_paid,copied,copy_fields,copyArguments,fields_paid,fields_vector]
  exact ⟨congrArg Prod.fst h,congrArg (fun q=>q.2.1) h,congrArg (fun q=>q.2.2) h⟩

theorem after_globals (cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)
    (hg:s.globals[p.globalIndex]?=some p.globalVector)(hv:p.globalVector.value=.i32 p.spVector):
    (after cfg s p).globals=s.globals:=by
  have vg:(vectorBefore s cfg.regularOpCost).globals[p.globalIndex]?=some p.globalVector:=by rw[vectorBefore,globals_paid];exact hg
  have restore: (vectorAfter cfg s p).globals=(vectorBefore s cfg.regularOpCost).globals:=by
    unfold vectorAfter
    exact StateDecodeVector.callAfter_globals cfg _ p.toVector hn.vector vg hv
  rw[after,finishStore,storeI32_globals,globals_paid,copied,copy_globals,copyArguments,globals_paid,restore,vectorBefore,globals_paid]

private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_store(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_vector(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout):view seed (vectorAfter cfg s p).host=view seed s.host:=by
  have h:=congrArg (view seed) (StateDecodeVector.callAfter_functional_host cfg (vectorBefore s cfg.regularOpCost) p.toVector)
  unfold vectorAfter
  change view seed (StateDecodeVector.callAfter cfg (vectorBefore s cfg.regularOpCost) p.toVector).host=view seed s.host
  have clean:view seed (StateDecodeVector.callAfter cfg (vectorBefore s cfg.regularOpCost) p.toVector).host=view seed (vectorBefore s cfg.regularOpCost).host:=h
  rw[clean,vectorBefore,view_paid]
private theorem view_copy(seed:NearState)(s:Store NearState)(op i:Nat)(out source:UInt32)(m:Memory)(n:Nat):
    view seed (UnwrapStateCopyEntry.callAfter s op i out source m n).host=view seed s.host:=by
  have h:=congrArg (view seed) (UnwrapStateCopyEffects.callAfter_host_frame s op i out source m n)
  exact h

theorem after_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  change view s.host (after cfg s p).host=s.host
  rw[after,finishStore,view_store,view_paid,copied,view_copy,copyArguments,view_paid,view_vector]
  rfl

theorem callAfter_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (callAfter cfg s p).mems[p.memoryIndex]?=some (finalMemory p):=by
  have mem:(entered s cfg.regularOpCost).mems[p.memoryIndex]?=some p.memory:=hm
  unfold callAfter
  exact after_memory cfg _ p hn mem

theorem callAfter_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    (callAfter cfg s p).funcs=s.funcs ∧ (callAfter cfg s p).modules=s.modules ∧ (callAfter cfg s p).tables=s.tables:=by
  unfold callAfter
  simpa only[entered,chargedStore] using after_fields cfg (entered s cfg.regularOpCost) p

theorem callAfter_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)
    (hg:s.globals[p.globalIndex]?=some p.globalVector)(hv:p.globalVector.value=.i32 p.spVector):
    (callAfter cfg s p).globals=s.globals:=by
  have global:(entered s cfg.regularOpCost).globals[p.globalIndex]?=some p.globalVector:=hg
  unfold callAfter
  simpa only[entered,chargedStore] using after_globals cfg (entered s cfg.regularOpCost) p hn global hv

theorem callAfter_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    {(callAfter cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=congrArg (view s.host) (after_functional_host cfg (entered s cfg.regularOpCost) p)
  change view s.host (callAfter cfg s p).host=s.host
  unfold callAfter
  have clean:view s.host (after cfg (entered s cfg.regularOpCost) p).host=view s.host (entered s cfg.regularOpCost).host:=h
  rw[clean]
  rfl
end WNear.Proofs.StateDecodeVectorCopy
