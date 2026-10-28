import Proofs.StateReadOuterFrames
import Proofs.StateReadOuterCode
import Proofs.StateReadOuterNative
import Proofs.StateReadOuterStorageCall

/-! Original219 resources transport through reserve96 and five real548
arguments. Canonical host Ready and fees are transported through charges only. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem ready_paid(s:Store NearState)(op n:Nat)(memory:Memory)(ctx:NearInterface.Context)
    (raw:NearInterface.RawStorage)(storage:List (List UInt8×List UInt8))(len ptr reg:UInt64)(key value:List UInt8)
    (hr:StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage len ptr reg key value):
    StorageReadCalls.Ready ⟨memory,(paid s op n).host⟩ ctx raw storage len ptr reg key value:=by
  induction n with
  |zero=>exact hr
  |succ n ih=>exact ih.charge _ op ctx raw storage len ptr reg key value
attribute [local irreducible] reserved storageArguments stored fee storageMemory

 theorem reserved_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (reserved s op p).mems[p.memoryIndex]?=some p.memory:=by
  rw[reserved,global_mems,paid_mems];exact hm
 theorem storageArguments_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (storageArguments s op p).mems[p.memoryIndex]?=some p.memory:=by
  rw[storageArguments,paid_mems];exact reserved_memory s op p hm

 theorem reserved_global(s:Store NearState)(op:Nat)(p:Layout)(hn:Native p)
    (hg:s.globals[p.globalIndex]?=some p.global219):
    (reserved s op p).globals[p.globalIndex]?=some p.global548:=by
  rw[reserved]
  simp only[setGlobal,paid_globals,Array.getElem?_modify,hg,Option.map_some,ite_true]
  rw[hn.storageGlobal]
 theorem storageArguments_global(s:Store NearState)(op:Nat)(p:Layout)(hn:Native p)
    (hg:s.globals[p.globalIndex]?=some p.global219):
    (storageArguments s op p).globals[p.globalIndex]?=some p.global548:=by
  rw[storageArguments,paid_globals];exact reserved_global s op p hn hg
 theorem storage_global_value(p:Layout)(hn:Native p):p.global548.value=.i32 p.sp548:=by
  rw[hn.storageGlobal,hn.storageSP]

 theorem reserved_code(s:Store NearState)(op inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):Code (reserved s op p) inst p extra a581 a236:=by
  have frame:=reserved_fields s op p
  exact hc.transport s _ inst p extra a581 a236 frame.1 frame.2.1 frame.2.2
 theorem storageArguments_code(s:Store NearState)(op inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):Code (storageArguments s op p) inst p extra a581 a236:=by
  have frame:=storageArguments_fields s op p
  exact hc.transport s _ inst p extra a581 a236 frame.1 frame.2.1 frame.2.2

 theorem reserved_ready(s:Store NearState)(op:Nat)(p:Layout)(ctx:NearInterface.Context)(raw:NearInterface.RawStorage)
    (storage:List (List UInt8×List UInt8))(key:List UInt8)
    (hr:StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes):
    StorageReadCalls.Ready ⟨p.memory,(reserved s op p).host⟩ ctx raw storage (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes:=by
  unfold reserved
  exact ready_paid s op 5 p.memory ctx raw storage _ _ _ key p.bytes hr
 theorem storageArguments_ready(s:Store NearState)(op:Nat)(p:Layout)(ctx:NearInterface.Context)(raw:NearInterface.RawStorage)
    (storage:List (List UInt8×List UInt8))(key:List UInt8)
    (hr:StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes):
    StorageReadCalls.Ready ⟨p.memory,(storageArguments s op p).host⟩ ctx raw storage (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes:=by
  unfold storageArguments
  exact ready_paid (reserved s op p) op 5 p.memory ctx raw storage _ _ _ key p.bytes (reserved_ready s op p ctx raw storage key hr)

private theorem fee_global(cfg:WasmConfig)(s:Store NearState)(i:Nat)(v:Value)(p:StateReadStorageOuter.Layout)
    (ctx:NearInterface.Context)(key:List UInt8):
    StateReadStorageOuter.fee cfg (setGlobal s i v) p ctx key=StateReadStorageOuter.fee cfg s p ctx key:=rfl
 theorem reserved_fee(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    fee cfg (reserved s cfg.regularOpCost p) p ctx key=fee cfg s p ctx key:=by
  unfold fee reserved
  rw[fee_global,storage_fee_paid]
 theorem storageArguments_fee(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    fee cfg (storageArguments s cfg.regularOpCost p) p ctx key=fee cfg s p ctx key:=by
  unfold fee storageArguments
  rw[storage_fee_paid]
  simpa only[fee] using reserved_fee cfg s p ctx key

 theorem reserved_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (5*op+rest)):
    (reserved s op p).host.gas.Credits rest:=by
  unfold reserved
  exact paid_credits s op 5 rest hc
 theorem storageArguments_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (10*op+rest)):
    (storageArguments s op p).host.gas.Credits rest:=by
  unfold storageArguments
  apply paid_credits
  exact reserved_credits s op (5*op+rest) p (hc.mono (by omega))

 theorem stored_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)
    (ctx:NearInterface.Context)(raw:NearInterface.RawStorage)(storage:List (List UInt8×List UInt8))(key:List UInt8)(rest:Nat)
    (hi:p.mi.memAddrs[0]?=some p.memoryIndex)(hm:s.mems[p.memoryIndex]?=some p.memory)
    (hr:StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hc:s.host.gas.Credits ((StateReadStorageOuter.bodyCost p.toStorage+22)*cfg.regularOpCost+fee cfg s p ctx key+rest)):
    (stored cfg s p ctx key).host.gas.Credits rest:=by
  have ready:=storageArguments_ready s cfg.regularOpCost p ctx raw storage key hr
  have memory:=storageArguments_memory s cfg.regularOpCost p hm
  have credits:(storageArguments s cfg.regularOpCost p).host.gas.Credits
      ((StateReadStorageOuter.bodyCost p.toStorage+12)*cfg.regularOpCost+fee cfg (storageArguments s cfg.regularOpCost p) p ctx key+rest):=by
    rw[storageArguments_fee]
    exact storageArguments_credits s cfg.regularOpCost _ p (hc.mono (by simp only[Nat.add_mul];omega))
  unfold fee at credits
  unfold stored
  exact StateReadStorageOuter.callAfter_credits cfg _ p.toStorage hn.storage ctx raw storage key rest hi memory ready credits

 theorem stored_memory(cfg:WasmConfig)(s:Store NearState)(limits:ExecLimits)(inst height:Nat)(callers:List CallFrame)
    (p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(extra a581 a236:Nat)(hn:Native p)
    (hc:Code s inst p extra a581 a236)(hm:s.mems[p.memoryIndex]?=some p.memory)
    (hg:s.globals[p.globalIndex]?=some p.global219)(hd:callers.length+4<limits.maxCallDepth):
    (stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p):=by
  have code:=storageArguments_code s cfg.regularOpCost inst p extra a581 a236 hc
  have memory:=storageArguments_memory s cfg.regularOpCost p hm
  have global:=storageArguments_global s cfg.regularOpCost p hn hg
  unfold stored storageMemory
  exact StateReadStorageOuter.callAfter_memory cfg _ limits inst height callers p.toStorage ctx key extra hn.storage hn.allocator code.storage memory global hd
end WNear.Proofs.StateReadOuter
