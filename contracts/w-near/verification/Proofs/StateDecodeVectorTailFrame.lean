import Proofs.StateDecodeVectorTail

namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
private theorem mems_paid (s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_global (s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem globals_paid (s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem tailAfter_memory (s:Store NearState)(op i gi:Nat)(m:Memory)(out scratch:UInt32)
    (hm:s.mems[i]?=some m) : (tailAfter s op i gi m out scratch).mems[i]?=some (tailMemory m out scratch):=by
  have cached:(paid s op 3).mems[i]?=some m:=by rw[mems_paid];exact hm
  have zeroBefore:(paid (paid s op 3) op 3).mems[i]?=some m:=by rw[mems_paid];exact cached
  have z:=storeI32_memory (paid (paid s op 3) op 3) i (out.toNat+8) m 0 zeroBefore
  have copyBefore:(paid (zeroStore (paid s op 3) op i m out) op 3).mems[i]?=some (writeI32 m (out.toNat+8) 0):=by
    rw[mems_paid];exact z
  have cp:=storeI64_memory (paid (zeroStore (paid s op 3) op i m out) op 3) i out.toNat
    (writeI32 m (out.toNat+8) 0) (readI64 m (scratch.toNat+8)) copyBefore
  simpa only[tailAfter,outputStore,StateDecodeScalar.store64Local,tailMemory,mems_global,mems_paid] using cp

private def fields (s:Store NearState):=(s.funcs,s.modules,s.tables)
private theorem fields_paid (s:Store NearState)(op n:Nat):fields (paid s op n)=fields s:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem fields_global (s:Store NearState)(i:Nat)(v:Value):fields (setGlobal s i v)=fields s:=rfl
private theorem fields_word (s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):fields (storeI64 s i a m v)=fields s:=rfl
private theorem fields_zero (s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):fields (storeI32 s i a m v)=fields s:=rfl
private theorem project (s t:Store NearState)(h:fields t=fields s):t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables:=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩

theorem tailAfter_fields (s:Store NearState)(op i gi:Nat)(m:Memory)(out scratch:UInt32):
    (tailAfter s op i gi m out scratch).funcs=s.funcs ∧(tailAfter s op i gi m out scratch).modules=s.modules ∧
    (tailAfter s op i gi m out scratch).tables=s.tables:=by
  apply project
  simp only[tailAfter,outputStore,StateDecodeScalar.store64Local,zeroStore,fields_paid,fields_global,fields_word,fields_zero]

private theorem globals_word (s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):(storeI64 s i a m v).globals=s.globals:=rfl
private theorem globals_zero (s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl

theorem tailAfter_globals (s:Store NearState)(op i gi:Nat)(m:Memory)(out scratch:UInt32):
    (tailAfter s op i gi m out scratch).globals=s.globals.modify gi (fun g=>{g with value:=.i32 (scratch+16)}):=by
  simp only[tailAfter,setGlobal,outputStore,StateDecodeScalar.store64Local,zeroStore,globals_paid,globals_word,globals_zero]

theorem tailAfter_credits (s:Store NearState)(op i gi rest:Nat)(m:Memory)(out scratch:UInt32)
    (hc:s.host.gas.Credits (13*op+rest)):(tailAfter s op i gi m out scratch).host.gas.Credits rest:=by
  simpa only[tailAfter,outputStore,StateDecodeScalar.store64Local,zeroStore,storeI64_host,storeI32_host,setGlobal,paid,chargedStore]
    using paid_credits s op 13 rest hc
end WNear.Proofs.StateDecodeVector
