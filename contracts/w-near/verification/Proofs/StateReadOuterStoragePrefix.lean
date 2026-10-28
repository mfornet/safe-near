import Proofs.StateReadOuterStorageCall
import Proofs.StateReadOuterNative
import Proofs.StateReadOuterCode
import Proofs.StateReadOuterFrames

/-! Actual219 reserve96 and the complete real548 storage call. The host hit,
code and global resources are all transported from the original caller state. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reserved stored StateReadStorageOuter.fee
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem global_host(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).host=s.host:=rfl
private theorem fee_global(cfg:WasmConfig)(s:Store NearState)(i:Nat)(v:Value)(p:StateReadStorageOuter.Layout)(ctx:NearInterface.Context)(key:List UInt8):
    StateReadStorageOuter.fee cfg (setGlobal s i v) p ctx key=StateReadStorageOuter.fee cfg s p ctx key:=by
  unfold StateReadStorageOuter.fee
  rfl

theorem storage_fee_reserved(cfg:WasmConfig)(s:Store NearState)(op:Nat)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    StateReadStorageOuter.fee cfg (reserved s op p) p.toStorage ctx key=StateReadStorageOuter.fee cfg s p.toStorage ctx key:=by
  rw[reserved,fee_global,storage_fee_paid]

theorem wp_storage_prefix(cfg:WasmConfig)(extra fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)
    (a581 a236:Nat)(ctx:NearInterface.Context)(raw:NearInterface.RawStorage)
    (storage:List (List UInt8×List UInt8))(key:List UInt8)(post:Post)
    (hn:Native p)(hcode:Code s frame.inst p extra a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global219)(hv:p.global219.value=.i32 p.sp219)
    (hs:2≤frame.locals.size)
    (hr:StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hd:callers.length+13<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((StateReadStorageOuter.bodyCost p.toStorage+22)*cfg.regularOpCost+fee cfg s p ctx key+rest))
    (hnext:WP cfg fuel (.next (atCode (stored cfg s p ctx key) limits base.toArray (reservedFrame frame p) callers code)) rest post):
    WP cfg (fuel+StateReadStorageOuter.bodySteps p.toStorage+12) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateReadOuter.setup++storageArgumentsCode++[.call 548]++code)))
      ((StateReadStorageOuter.bodyCost p.toStorage+22)*cfg.regularOpCost+fee cfg s p ctx key+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=reserved s op p
  let f:=reservedFrame frame p
  have fs:=reserved_fields s op p
  have co:StateReadStorageOuter.Code active f.inst p.toStorage extra:=hcode.storage.transport s active frame.inst p.toStorage extra fs.1 fs.2.1 fs.2.2
  have mm:active.mems[p.memoryIndex]?=some p.memory:=by dsimp only[active];rw[reserved,global_mems,paid_mems];exact hm
  have gg:active.globals[p.globalIndex]?=some p.global548:=by
    rw[hn.storageGlobal]
    simp only[active,reserved,paid_globals,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]
  have vv:p.global548.value=.i32 p.sp548:=by rw[hn.storageGlobal,hn.storageSP]
  have ready(n:Nat):StorageReadCalls.Ready ⟨p.memory,(paid s op n).host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes:=by
    induction n with|zero=>exact hr|succ n ih=>exact ih.charge _ op ctx raw storage _ _ _ key p.bytes
  have ra:StorageReadCalls.Ready ⟨p.memory,active.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes:=by
    simpa only[active,reserved,global_host] using ready 5
  have af:StateReadStorageOuter.fee cfg active p.toStorage ctx key=fee cfg s p ctx key:=storage_fee_reserved cfg s op p ctx key
  have ca:active.host.gas.Credits ((StateReadStorageOuter.bodyCost p.toStorage+17)*op+StateReadStorageOuter.fee cfg active p.toStorage ctx key+rest):=by
    rw[af]
    simpa only[active,reserved,global_host] using paid_credits s op 5 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have next:WP cfg fuel (.next (atCode (StateReadStorageOuter.callAfter cfg (paid active op 5) p.toStorage ctx key) limits base.toArray f callers code)) rest post:=by
    simpa only[stored,storageArguments,active,f,op] using hnext
  have child:=wp_storage_call cfg extra fuel rest active limits base f callers code (scratch p) p.toStorage p.address548 ctx raw storage key post hn.storage co hn.allocator
    hn.storageOut hn.keyPointer hn.keyLength mm gg vv (by simp[f,reservedFrame,show 1<frame.locals.size by omega]) ra hcode.index548 (by rw[fs.1];exact hcode.function548) hd ca next
  rw[af] at child
  have prefixWP:=wp_setup cfg (fuel+StateReadStorageOuter.bodySteps p.toStorage+7)
    ((StateReadStorageOuter.bodyCost p.toStorage+17)*op+fee cfg s p ctx key+rest) s limits base.toArray frame callers
    (storageArgumentsCode++[.call 548]++code) p post (hcode.module s frame.inst p extra a581 a236) (hcode.globalIndex s frame.inst p extra a581 a236) hg hv
    (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega)) child
  have ce:5*cfg.regularOpCost+((StateReadStorageOuter.bodyCost p.toStorage+17)*op+fee cfg s p ctx key+rest)=
      (StateReadStorageOuter.bodyCost p.toStorage+22)*cfg.regularOpCost+fee cfg s p ctx key+rest:=by dsimp[op];simp only[Nat.add_mul];omega
  rw[ce] at prefixWP
  simpa only[List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using prefixWP
end WNear.Proofs.StateReadOuter
