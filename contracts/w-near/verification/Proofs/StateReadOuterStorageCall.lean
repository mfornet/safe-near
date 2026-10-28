import Proofs.StateReadOuterArguments
import Proofs.StateReadStorageOuterCall

/-! The actual219 storage arguments and the real548 call, over an arbitrary
pre-store. Original host hit data are transported only through actual charges. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode StateReadStorageOuter.callAfter StateReadStorageOuter.fee
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem storage_fee_paid(cfg:WasmConfig)(s:Store NearState)(op n:Nat)(p:StateReadStorageOuter.Layout)
    (ctx:NearInterface.Context)(key:List UInt8):
    StateReadStorageOuter.fee cfg (paid s op n) p ctx key=StateReadStorageOuter.fee cfg s p ctx key:=by
  induction n with
  |zero=>rfl
  |succ n ih=>exact (StateReadStorageOuter.fee_charge cfg (paid s op n) op p ctx key).trans ih

theorem wp_storage_call(cfg:WasmConfig)(extra fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (p:StateReadStorageOuter.Layout)(address:Nat)(ctx:NearInterface.Context)(raw:NearInterface.RawStorage)
    (storage:List (List UInt8×List UInt8))(key:List UInt8)(post:Post)
    (hn:StateReadStorageOuter.Native p)(hcode:StateReadStorageOuter.Code s frame.inst p extra)
    (ha:p.allocator=1074896)(hout:p.out548=r+8)(hptr:p.keyPtr=1049788)(hlen:p.keyLen=5)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global548)(hv:p.global548.value=.i32 p.sp548)
    (h1:frame.locals[1]?=some (.i32 r))
    (hr:StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hi:p.mi.funcAddrs[548]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateReadStorageOuter.signature frame.inst WNear.Binary.StateReadStorageOuter.function))
    (hd:callers.length+13<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((StateReadStorageOuter.bodyCost p+17)*cfg.regularOpCost+StateReadStorageOuter.fee cfg s p ctx key+rest))
    (hnext:WP cfg fuel (.next (atCode (StateReadStorageOuter.callAfter cfg (paid s cfg.regularOpCost 5) p ctx key)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+StateReadStorageOuter.bodySteps p+7) (.next (atCode s limits base.toArray frame callers
      (storageArgumentsCode++[.call 548]++code)))
      ((StateReadStorageOuter.bodyCost p+17)*cfg.regularOpCost+StateReadStorageOuter.fee cfg s p ctx key+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=paid s op 5
  have ready(n:Nat):StorageReadCalls.Ready ⟨p.memory,(paid s op n).host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes:=by
    induction n with
    |zero=>exact hr
    |succ n ih=>exact ih.charge _ op ctx raw storage _ _ _ key p.bytes
  have co:StateReadStorageOuter.Code active frame.inst p extra:=hcode.transport s active frame.inst p extra (paid_funcs s op 5) (paid_modules s op 5) (paid_tables s op 5)
  have cc:active.host.gas.Credits ((StateReadStorageOuter.bodyCost p+12)*op+StateReadStorageOuter.fee cfg active p ctx key+rest):=by
    rw[storage_fee_paid]
    exact paid_credits s op 5 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have call:=StateReadStorageOuter.wp_call cfg extra fuel rest active limits base frame callers code p address ctx raw storage key post hn co ha
    (by rw[paid_mems];exact hm) (by rw[paid_globals];exact hg) hv (ready 5) hi (by rw[paid_funcs];exact hf) hd cc hnext
  have arr:(base++[Value.i32 p.out548,.i32 p.keyPtr,.i32 p.keyLen]).toArray=
      ((base.toArray.push (.i32 (r+8))).push (.i32 1049788)).push (.i32 5):=by rw[hout,hptr,hlen];apply Array.toList_inj.mp;simp
  have next:WP cfg (fuel+StateReadStorageOuter.bodySteps p+2) (.next (atCode active limits
      (((base.toArray.push (.i32 (r+8))).push (.i32 1049788)).push (.i32 5)) frame callers (.call 548::code)))
      ((StateReadStorageOuter.bodyCost p+12)*op+StateReadStorageOuter.fee cfg s p ctx key+rest) post:=by
    have af:StateReadStorageOuter.fee cfg active p ctx key=StateReadStorageOuter.fee cfg s p ctx key:=storage_fee_paid cfg s op 5 p ctx key
    rw[af,arr] at call
    exact call
  have args:=wp_storage_arguments cfg (fuel+StateReadStorageOuter.bodySteps p+2)
    ((StateReadStorageOuter.bodyCost p+12)*op+StateReadStorageOuter.fee cfg s p ctx key+rest) s limits base.toArray frame callers (.call 548::code) r 0 post h1
    (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega)) next
  have ce:5*cfg.regularOpCost+((StateReadStorageOuter.bodyCost p+12)*op+StateReadStorageOuter.fee cfg s p ctx key+rest)=
      (StateReadStorageOuter.bodyCost p+17)*cfg.regularOpCost+StateReadStorageOuter.fee cfg s p ctx key+rest:=by dsimp[op];simp only[Nat.add_mul];omega
  rw[ce] at args
  simpa only[List.singleton_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.StateReadOuter
