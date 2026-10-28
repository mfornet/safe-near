import Proofs.StateReadOuterState
import Proofs.StateReadStorageOuterResult
import Proofs.StateDecodeBorshReadResult
import Proofs.UnwrapStateCopyEffects

/-! Installed functions, modules and tables are unchanged by every219 phase. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private def fields(s:Store NearState):=(s.funcs,s.modules,s.tables)
private theorem paid_fields(s:Store NearState)(op n:Nat):fields (paid s op n)=fields s:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_fields(s:Store NearState)(i:Nat)(v:Value):fields (setGlobal s i v)=fields s:=rfl
private theorem charge_fields(s:Store NearState)(op:Nat):fields (chargedStore s op)=fields s:=rfl
private theorem word_fields(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):fields (storeI32 s i a m v)=fields s:=rfl
private theorem wide_fields(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):fields (storeI64 s i a m v)=fields s:=rfl
private theorem storage_fields(cfg:WasmConfig)(s:Store NearState)(p:StateReadStorageOuter.Layout)(ctx:NearInterface.Context)(key:List UInt8):
    fields (StateReadStorageOuter.callAfter cfg s p ctx key)=fields s:=by
  have h:=StateReadStorageOuter.callAfter_fields cfg s p ctx key
  simp only[fields,h.1,h.2.1,h.2.2]
private theorem copied_fields(s:Store NearState)(op i:Nat)(m:Memory)(r:UInt32):fields (copiedStorage s op i m r)=fields s:=by
  rw[copiedStorage,storageLowStore,wide_fields,paid_fields,storageHighStore,word_fields,paid_fields]
private theorem pack_call_fields(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory):
    fields (PackWordsCall.callAfter s op i out src m)=fields s:=by
  have h:=PackWordsCall.callAfter_frame s op i out src m
  simp only[fields,h.1,h.2.1,h.2.2.2.1]
private theorem decoder_fields(cfg:WasmConfig)(s:Store NearState)(p:StateDecodeBorshRead.Layout)(q:StateDecodeVectorCopy.Layout):
    fields (StateDecodeBorshRead.callAfter cfg s p q)=fields s:=by
  have h:=StateDecodeBorshRead.callAfter_fields cfg s p q
  simp only[fields,h.1,h.2.1,h.2.2]
private theorem copy_fields(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory)(n:Nat):
    fields (UnwrapStateCopyEntry.callAfter s op i out src m n)=fields s:=by
  have h:=congrArg fields (UnwrapStateCopyEffects.callAfter_resources s op i out src m n)
  exact h
private theorem release_fields(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    fields (VectorDropInsert.callAfter s op q)=fields s:=by
  have h:=VectorDropInsert.callAfter_fields s op q
  simp only[fields,h.1,h.2.1,h.2.2.2]
attribute [local irreducible] fields
attribute [local irreducible] reserved storageArguments stored presenceChecked storageCopied packArguments packed decodeArguments decoded decodeGuarded copyArguments outputCopied outputDropped releaseArguments released restored after

private theorem reserved_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (reserved s op p)=fields s:=by
  rw[reserved,global_fields,paid_fields]

theorem reserved_fields(s:Store NearState)(op:Nat)(p:Layout):
    (reserved s op p).funcs=s.funcs ∧(reserved s op p).modules=s.modules ∧(reserved s op p).tables=s.tables:=by
  have h:=reserved_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem storageArguments_fields_eq(s:Store NearState)(op:Nat)(p:Layout):fields (storageArguments s op p)=fields s:=by
  rw[storageArguments,paid_fields]
  exact reserved_fields_eq s op p

theorem storageArguments_fields(s:Store NearState)(op:Nat)(p:Layout):
    (storageArguments s op p).funcs=s.funcs ∧(storageArguments s op p).modules=s.modules ∧(storageArguments s op p).tables=s.tables:=by
  have h:=storageArguments_fields_eq s op p
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem stored_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (stored cfg s p ctx key)=fields s:=by
  rw[stored,storage_fields]
  exact storageArguments_fields_eq s cfg.regularOpCost p

theorem stored_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (stored cfg s p ctx key).funcs=s.funcs ∧(stored cfg s p ctx key).modules=s.modules ∧(stored cfg s p ctx key).tables=s.tables:=by
  have h:=stored_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem presenceChecked_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (presenceChecked cfg s p ctx key)=fields s:=by
  rw[presenceChecked,paid_fields]
  exact stored_fields_eq cfg s p ctx key

theorem presenceChecked_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (presenceChecked cfg s p ctx key).funcs=s.funcs ∧(presenceChecked cfg s p ctx key).modules=s.modules ∧(presenceChecked cfg s p ctx key).tables=s.tables:=by
  have h:=presenceChecked_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem storageCopied_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (storageCopied cfg s p ctx key)=fields s:=by
  rw[storageCopied,copied_fields]
  exact presenceChecked_fields_eq cfg s p ctx key

theorem storageCopied_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (storageCopied cfg s p ctx key).funcs=s.funcs ∧(storageCopied cfg s p ctx key).modules=s.modules ∧(storageCopied cfg s p ctx key).tables=s.tables:=by
  have h:=storageCopied_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem packArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (packArguments cfg s p ctx key)=fields s:=by
  rw[packArguments,paid_fields]
  exact storageCopied_fields_eq cfg s p ctx key

theorem packArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (packArguments cfg s p ctx key).funcs=s.funcs ∧(packArguments cfg s p ctx key).modules=s.modules ∧(packArguments cfg s p ctx key).tables=s.tables:=by
  have h:=packArguments_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem packed_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (packed cfg s p ctx key)=fields s:=by
  rw[packed,pack_call_fields]
  exact packArguments_fields_eq cfg s p ctx key

theorem packed_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (packed cfg s p ctx key).funcs=s.funcs ∧(packed cfg s p ctx key).modules=s.modules ∧(packed cfg s p ctx key).tables=s.tables:=by
  have h:=packed_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem decodeArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (decodeArguments cfg s p ctx key)=fields s:=by
  rw[decodeArguments,paid_fields]
  exact packed_fields_eq cfg s p ctx key

theorem decodeArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (decodeArguments cfg s p ctx key).funcs=s.funcs ∧(decodeArguments cfg s p ctx key).modules=s.modules ∧(decodeArguments cfg s p ctx key).tables=s.tables:=by
  have h:=decodeArguments_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem decoded_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (decoded cfg s p ctx key)=fields s:=by
  rw[decoded,decoder_fields]
  exact decodeArguments_fields_eq cfg s p ctx key

theorem decoded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (decoded cfg s p ctx key).funcs=s.funcs ∧(decoded cfg s p ctx key).modules=s.modules ∧(decoded cfg s p ctx key).tables=s.tables:=by
  have h:=decoded_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem decodeGuarded_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (decodeGuarded cfg s p ctx key)=fields s:=by
  rw[decodeGuarded,paid_fields]
  exact decoded_fields_eq cfg s p ctx key

theorem decodeGuarded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (decodeGuarded cfg s p ctx key).funcs=s.funcs ∧(decodeGuarded cfg s p ctx key).modules=s.modules ∧(decodeGuarded cfg s p ctx key).tables=s.tables:=by
  have h:=decodeGuarded_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem copyArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (copyArguments cfg s p ctx key)=fields s:=by
  rw[copyArguments,paid_fields]
  exact decodeGuarded_fields_eq cfg s p ctx key

theorem copyArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (copyArguments cfg s p ctx key).funcs=s.funcs ∧(copyArguments cfg s p ctx key).modules=s.modules ∧(copyArguments cfg s p ctx key).tables=s.tables:=by
  have h:=copyArguments_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem outputCopied_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (outputCopied cfg s p ctx key)=fields s:=by
  rw[outputCopied,copy_fields]
  exact copyArguments_fields_eq cfg s p ctx key

theorem outputCopied_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (outputCopied cfg s p ctx key).funcs=s.funcs ∧(outputCopied cfg s p ctx key).modules=s.modules ∧(outputCopied cfg s p ctx key).tables=s.tables:=by
  have h:=outputCopied_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem outputDropped_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (outputDropped cfg s p ctx key)=fields s:=by
  rw[outputDropped,paid_fields]
  exact outputCopied_fields_eq cfg s p ctx key

theorem outputDropped_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (outputDropped cfg s p ctx key).funcs=s.funcs ∧(outputDropped cfg s p ctx key).modules=s.modules ∧(outputDropped cfg s p ctx key).tables=s.tables:=by
  have h:=outputDropped_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem releaseArguments_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (releaseArguments cfg s p ctx key)=fields s:=by
  rw[releaseArguments,paid_fields]
  exact outputDropped_fields_eq cfg s p ctx key

theorem releaseArguments_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (releaseArguments cfg s p ctx key).funcs=s.funcs ∧(releaseArguments cfg s p ctx key).modules=s.modules ∧(releaseArguments cfg s p ctx key).tables=s.tables:=by
  have h:=releaseArguments_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem released_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (released cfg s p ctx key)=fields s:=by
  rw[released,release_fields]
  exact releaseArguments_fields_eq cfg s p ctx key

theorem released_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (released cfg s p ctx key).funcs=s.funcs ∧(released cfg s p ctx key).modules=s.modules ∧(released cfg s p ctx key).tables=s.tables:=by
  have h:=released_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem restored_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (restored cfg s p ctx key)=fields s:=by
  rw[restored,global_fields,paid_fields]
  exact released_fields_eq cfg s p ctx key

theorem restored_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (restored cfg s p ctx key).funcs=s.funcs ∧(restored cfg s p ctx key).modules=s.modules ∧(restored cfg s p ctx key).tables=s.tables:=by
  have h:=restored_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)

private theorem after_fields_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):fields (after cfg s p ctx key)=fields s:=by
  rw[after,charge_fields]
  exact restored_fields_eq cfg s p ctx key

theorem after_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    (after cfg s p ctx key).funcs=s.funcs ∧(after cfg s p ctx key).modules=s.modules ∧(after cfg s p ctx key).tables=s.tables:=by
  have h:=after_fields_eq cfg s p ctx key
  have a:=congrArg (fun t=>t.1) h
  have b:=congrArg (fun t=>t.2.1) h
  have c:=congrArg (fun t=>t.2.2) h
  simpa only[fields] using And.intro a (And.intro b c)
end WNear.Proofs.StateReadOuter
