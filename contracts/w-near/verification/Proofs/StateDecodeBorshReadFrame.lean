import Proofs.StateDecodeBorshReadPhases
import Proofs.StateDecodeBorshWrapperResult

/-! Exact code-array and functional-host frames for every accepted161 phase. -/
namespace WNear.Proofs.StateDecodeBorshRead
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
private theorem child_fields (cfg:WasmConfig)(s:Store NearState)(p:StateDecodeBorshWrapper.Layout)(q:StateDecodeVectorCopy.Layout):
    fields (StateDecodeBorshWrapper.callAfter cfg s p q)=fields s:=by
  have h:=StateDecodeBorshWrapper.callAfter_fields cfg s p q
  simp only[fields,h.1,h.2.1,h.2.2]
private theorem charge_fields(s:Store NearState)(op:Nat):fields (chargedStore s op)=fields s:=rfl
attribute [local irreducible] fields
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
private theorem view_child(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:StateDecodeBorshWrapper.Layout)(q:StateDecodeVectorCopy.Layout):
    view seed (StateDecodeBorshWrapper.callAfter cfg s p q).host=view seed s.host:=by
  exact view_rebase seed s.host _ (StateDecodeBorshWrapper.callAfter_functional_host cfg s p q)
private theorem view_charge(seed:NearState)(s:Store NearState)(op:Nat):view seed (chargedStore s op).host=view seed s.host:=rfl
attribute [local irreducible] view

attribute [local irreducible] reserved highSaved sliceSaved wrapperArguments wrapped packedCached tagCached firstCopyArguments firstCopied firstDropped guarded upperSaved acceptedCopyArguments acceptedCopied acceptedDropped exhausted resultCopyArguments resultCopied resultDropped tagged branched after

private theorem reserved_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (reserved s op p)=fields s:=by
  rw[reserved,global_fields,paid_fields]


private theorem view_reserved(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (reserved s op p).host=view seed s.host:=by
  rw[reserved,view_global,view_paid]


theorem reserved_fields(s:Store NearState)(op:Nat)(p:Layout):
    (reserved s op p).funcs=s.funcs ∧(reserved s op p).modules=s.modules ∧(reserved s op p).tables=s.tables:=by
  have h:=reserved_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem reserved_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(reserved s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_reserved s.host s op p
  simpa only[view] using h

private theorem highSaved_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (highSaved s op p)=fields s:=by
  rw[highSaved,word_fields,paid_fields]
  exact reserved_fields_eq s op p

private theorem view_highSaved(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (highSaved s op p).host=view seed s.host:=by
  rw[highSaved,view_word,view_paid]
  exact view_reserved seed s op p

theorem highSaved_fields(s:Store NearState)(op:Nat)(p:Layout):
    (highSaved s op p).funcs=s.funcs ∧(highSaved s op p).modules=s.modules ∧(highSaved s op p).tables=s.tables:=by
  have h:=highSaved_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem highSaved_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(highSaved s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_highSaved s.host s op p
  simpa only[view] using h

private theorem sliceSaved_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (sliceSaved s op p)=fields s:=by
  rw[sliceSaved,word_fields,paid_fields]
  exact highSaved_fields_eq s op p

private theorem view_sliceSaved(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (sliceSaved s op p).host=view seed s.host:=by
  rw[sliceSaved,view_word,view_paid]
  exact view_highSaved seed s op p

theorem sliceSaved_fields(s:Store NearState)(op:Nat)(p:Layout):
    (sliceSaved s op p).funcs=s.funcs ∧(sliceSaved s op p).modules=s.modules ∧(sliceSaved s op p).tables=s.tables:=by
  have h:=sliceSaved_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem sliceSaved_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(sliceSaved s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_sliceSaved s.host s op p
  simpa only[view] using h

private theorem wrapperArguments_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (wrapperArguments s op p)=fields s:=by
  rw[wrapperArguments,paid_fields]
  exact sliceSaved_fields_eq s op p

private theorem view_wrapperArguments(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (wrapperArguments s op p).host=view seed s.host:=by
  rw[wrapperArguments,view_paid]
  exact view_sliceSaved seed s op p

theorem wrapperArguments_fields(s:Store NearState)(op:Nat)(p:Layout):
    (wrapperArguments s op p).funcs=s.funcs ∧(wrapperArguments s op p).modules=s.modules ∧(wrapperArguments s op p).tables=s.tables:=by
  have h:=wrapperArguments_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem wrapperArguments_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(wrapperArguments s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_wrapperArguments s.host s op p
  simpa only[view] using h

private theorem wrapped_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (wrapped cfg s p q)=fields s:=by
  rw[wrapped,child_fields]
  exact wrapperArguments_fields_eq s cfg.regularOpCost p

private theorem view_wrapped(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (wrapped cfg s p q).host=view seed s.host:=by
  rw[wrapped,view_child]
  exact view_wrapperArguments seed s cfg.regularOpCost p

theorem wrapped_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wrapped cfg s p q).funcs=s.funcs ∧(wrapped cfg s p q).modules=s.modules ∧(wrapped cfg s p q).tables=s.tables:=by
  have h:=wrapped_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem wrapped_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(wrapped cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_wrapped s.host cfg s p q
  simpa only[view] using h

private theorem packedCached_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (packedCached cfg s p q)=fields s:=by
  rw[packedCached,paid_fields]
  exact wrapped_fields_eq cfg s p q

private theorem view_packedCached(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (packedCached cfg s p q).host=view seed s.host:=by
  rw[packedCached,view_paid]
  exact view_wrapped seed cfg s p q

theorem packedCached_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedCached cfg s p q).funcs=s.funcs ∧(packedCached cfg s p q).modules=s.modules ∧(packedCached cfg s p q).tables=s.tables:=by
  have h:=packedCached_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem packedCached_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(packedCached cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_packedCached s.host cfg s p q
  simpa only[view] using h

private theorem tagCached_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (tagCached cfg s p q)=fields s:=by
  rw[tagCached,paid_fields]
  exact packedCached_fields_eq cfg s p q

private theorem view_tagCached(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (tagCached cfg s p q).host=view seed s.host:=by
  rw[tagCached,view_paid]
  exact view_packedCached seed cfg s p q

theorem tagCached_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagCached cfg s p q).funcs=s.funcs ∧(tagCached cfg s p q).modules=s.modules ∧(tagCached cfg s p q).tables=s.tables:=by
  have h:=tagCached_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem tagCached_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(tagCached cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_tagCached s.host cfg s p q
  simpa only[view] using h

private theorem firstCopyArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (firstCopyArguments cfg s p q)=fields s:=by
  rw[firstCopyArguments,paid_fields]
  exact tagCached_fields_eq cfg s p q

private theorem view_firstCopyArguments(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (firstCopyArguments cfg s p q).host=view seed s.host:=by
  rw[firstCopyArguments,view_paid]
  exact view_tagCached seed cfg s p q

theorem firstCopyArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (firstCopyArguments cfg s p q).funcs=s.funcs ∧(firstCopyArguments cfg s p q).modules=s.modules ∧(firstCopyArguments cfg s p q).tables=s.tables:=by
  have h:=firstCopyArguments_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem firstCopyArguments_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(firstCopyArguments cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_firstCopyArguments s.host cfg s p q
  simpa only[view] using h

private theorem firstCopied_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (firstCopied cfg s p q)=fields s:=by
  rw[firstCopied,copy_fields]
  exact firstCopyArguments_fields_eq cfg s p q

private theorem view_firstCopied(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (firstCopied cfg s p q).host=view seed s.host:=by
  rw[firstCopied,view_copy]
  exact view_firstCopyArguments seed cfg s p q

theorem firstCopied_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (firstCopied cfg s p q).funcs=s.funcs ∧(firstCopied cfg s p q).modules=s.modules ∧(firstCopied cfg s p q).tables=s.tables:=by
  have h:=firstCopied_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem firstCopied_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(firstCopied cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_firstCopied s.host cfg s p q
  simpa only[view] using h

private theorem firstDropped_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (firstDropped cfg s p q)=fields s:=by
  rw[firstDropped,paid_fields]
  exact firstCopied_fields_eq cfg s p q

private theorem view_firstDropped(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (firstDropped cfg s p q).host=view seed s.host:=by
  rw[firstDropped,view_paid]
  exact view_firstCopied seed cfg s p q

theorem firstDropped_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (firstDropped cfg s p q).funcs=s.funcs ∧(firstDropped cfg s p q).modules=s.modules ∧(firstDropped cfg s p q).tables=s.tables:=by
  have h:=firstDropped_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem firstDropped_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(firstDropped cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_firstDropped s.host cfg s p q
  simpa only[view] using h

private theorem guarded_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (guarded cfg s p q)=fields s:=by
  rw[guarded,paid_fields]
  exact firstDropped_fields_eq cfg s p q

private theorem view_guarded(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (guarded cfg s p q).host=view seed s.host:=by
  rw[guarded,view_paid]
  exact view_firstDropped seed cfg s p q

theorem guarded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (guarded cfg s p q).funcs=s.funcs ∧(guarded cfg s p q).modules=s.modules ∧(guarded cfg s p q).tables=s.tables:=by
  have h:=guarded_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem guarded_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(guarded cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_guarded s.host cfg s p q
  simpa only[view] using h

private theorem upperSaved_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (upperSaved cfg s p q)=fields s:=by
  rw[upperSaved,word_fields,paid_fields]
  exact guarded_fields_eq cfg s p q

private theorem view_upperSaved(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (upperSaved cfg s p q).host=view seed s.host:=by
  rw[upperSaved,view_word,view_paid]
  exact view_guarded seed cfg s p q

theorem upperSaved_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (upperSaved cfg s p q).funcs=s.funcs ∧(upperSaved cfg s p q).modules=s.modules ∧(upperSaved cfg s p q).tables=s.tables:=by
  have h:=upperSaved_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem upperSaved_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(upperSaved cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_upperSaved s.host cfg s p q
  simpa only[view] using h

private theorem acceptedCopyArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (acceptedCopyArguments cfg s p q)=fields s:=by
  rw[acceptedCopyArguments,paid_fields]
  exact upperSaved_fields_eq cfg s p q

private theorem view_acceptedCopyArguments(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (acceptedCopyArguments cfg s p q).host=view seed s.host:=by
  rw[acceptedCopyArguments,view_paid]
  exact view_upperSaved seed cfg s p q

theorem acceptedCopyArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (acceptedCopyArguments cfg s p q).funcs=s.funcs ∧(acceptedCopyArguments cfg s p q).modules=s.modules ∧(acceptedCopyArguments cfg s p q).tables=s.tables:=by
  have h:=acceptedCopyArguments_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem acceptedCopyArguments_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(acceptedCopyArguments cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_acceptedCopyArguments s.host cfg s p q
  simpa only[view] using h

private theorem acceptedCopied_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (acceptedCopied cfg s p q)=fields s:=by
  rw[acceptedCopied,copy_fields]
  exact acceptedCopyArguments_fields_eq cfg s p q

private theorem view_acceptedCopied(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (acceptedCopied cfg s p q).host=view seed s.host:=by
  rw[acceptedCopied,view_copy]
  exact view_acceptedCopyArguments seed cfg s p q

theorem acceptedCopied_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (acceptedCopied cfg s p q).funcs=s.funcs ∧(acceptedCopied cfg s p q).modules=s.modules ∧(acceptedCopied cfg s p q).tables=s.tables:=by
  have h:=acceptedCopied_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem acceptedCopied_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(acceptedCopied cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_acceptedCopied s.host cfg s p q
  simpa only[view] using h

private theorem acceptedDropped_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (acceptedDropped cfg s p q)=fields s:=by
  rw[acceptedDropped,paid_fields]
  exact acceptedCopied_fields_eq cfg s p q

private theorem view_acceptedDropped(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (acceptedDropped cfg s p q).host=view seed s.host:=by
  rw[acceptedDropped,view_paid]
  exact view_acceptedCopied seed cfg s p q

theorem acceptedDropped_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (acceptedDropped cfg s p q).funcs=s.funcs ∧(acceptedDropped cfg s p q).modules=s.modules ∧(acceptedDropped cfg s p q).tables=s.tables:=by
  have h:=acceptedDropped_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem acceptedDropped_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(acceptedDropped cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_acceptedDropped s.host cfg s p q
  simpa only[view] using h

private theorem exhausted_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (exhausted cfg s p q)=fields s:=by
  rw[exhausted,paid_fields]
  exact acceptedDropped_fields_eq cfg s p q

private theorem view_exhausted(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (exhausted cfg s p q).host=view seed s.host:=by
  rw[exhausted,view_paid]
  exact view_acceptedDropped seed cfg s p q

theorem exhausted_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (exhausted cfg s p q).funcs=s.funcs ∧(exhausted cfg s p q).modules=s.modules ∧(exhausted cfg s p q).tables=s.tables:=by
  have h:=exhausted_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem exhausted_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(exhausted cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_exhausted s.host cfg s p q
  simpa only[view] using h

private theorem resultCopyArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (resultCopyArguments cfg s p q)=fields s:=by
  rw[resultCopyArguments,paid_fields]
  exact exhausted_fields_eq cfg s p q

private theorem view_resultCopyArguments(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (resultCopyArguments cfg s p q).host=view seed s.host:=by
  rw[resultCopyArguments,view_paid]
  exact view_exhausted seed cfg s p q

theorem resultCopyArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (resultCopyArguments cfg s p q).funcs=s.funcs ∧(resultCopyArguments cfg s p q).modules=s.modules ∧(resultCopyArguments cfg s p q).tables=s.tables:=by
  have h:=resultCopyArguments_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem resultCopyArguments_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(resultCopyArguments cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_resultCopyArguments s.host cfg s p q
  simpa only[view] using h

private theorem resultCopied_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (resultCopied cfg s p q)=fields s:=by
  rw[resultCopied,copy_fields]
  exact resultCopyArguments_fields_eq cfg s p q

private theorem view_resultCopied(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (resultCopied cfg s p q).host=view seed s.host:=by
  rw[resultCopied,view_copy]
  exact view_resultCopyArguments seed cfg s p q

theorem resultCopied_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (resultCopied cfg s p q).funcs=s.funcs ∧(resultCopied cfg s p q).modules=s.modules ∧(resultCopied cfg s p q).tables=s.tables:=by
  have h:=resultCopied_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem resultCopied_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(resultCopied cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_resultCopied s.host cfg s p q
  simpa only[view] using h

private theorem resultDropped_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (resultDropped cfg s p q)=fields s:=by
  rw[resultDropped,paid_fields]
  exact resultCopied_fields_eq cfg s p q

private theorem view_resultDropped(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (resultDropped cfg s p q).host=view seed s.host:=by
  rw[resultDropped,view_paid]
  exact view_resultCopied seed cfg s p q

theorem resultDropped_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (resultDropped cfg s p q).funcs=s.funcs ∧(resultDropped cfg s p q).modules=s.modules ∧(resultDropped cfg s p q).tables=s.tables:=by
  have h:=resultDropped_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem resultDropped_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(resultDropped cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_resultDropped s.host cfg s p q
  simpa only[view] using h

private theorem tagged_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (tagged cfg s p q)=fields s:=by
  rw[tagged,word_fields,paid_fields]
  exact resultDropped_fields_eq cfg s p q

private theorem view_tagged(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (tagged cfg s p q).host=view seed s.host:=by
  rw[tagged,view_word,view_paid]
  exact view_resultDropped seed cfg s p q

theorem tagged_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagged cfg s p q).funcs=s.funcs ∧(tagged cfg s p q).modules=s.modules ∧(tagged cfg s p q).tables=s.tables:=by
  have h:=tagged_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem tagged_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(tagged cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_tagged s.host cfg s p q
  simpa only[view] using h

private theorem branched_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (branched cfg s p q)=fields s:=by
  rw[branched,charge_fields]
  exact tagged_fields_eq cfg s p q

private theorem view_branched(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (branched cfg s p q).host=view seed s.host:=by
  rw[branched,view_charge]
  exact view_tagged seed cfg s p q

theorem branched_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (branched cfg s p q).funcs=s.funcs ∧(branched cfg s p q).modules=s.modules ∧(branched cfg s p q).tables=s.tables:=by
  have h:=branched_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem branched_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(branched cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_branched s.host cfg s p q
  simpa only[view] using h

private theorem after_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):fields (after cfg s p q)=fields s:=by
  rw[after,global_fields,paid_fields]
  exact branched_fields_eq cfg s p q

private theorem view_after(seed:NearState)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):view seed (after cfg s p q).host=view seed s.host:=by
  rw[after,view_global,view_paid]
  exact view_branched seed cfg s p q

theorem after_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (after cfg s p q).funcs=s.funcs ∧(after cfg s p q).modules=s.modules ∧(after cfg s p q).tables=s.tables:=by
  have h:=after_fields_eq cfg s p q
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

theorem after_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(after cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=view_after s.host cfg s p q
  simpa only[view] using h
end WNear.Proofs.StateDecodeBorshRead
