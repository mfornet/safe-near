import Proofs.StateDecodePrefixOutputState

namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem cached_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (cached s op).mems[p.index]?=some p.memory:=by rw[cached,mems_paid];exact hm
theorem high_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (high s op p).mems[p.index]?=some (highMemory p):=by
  unfold high outputHighStore highMemory
  apply storeI32_memory
  rw[mems_paid,cached,mems_paid];exact hm
theorem low_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (low s op p).mems[p.index]?=some (lowMemory p):=by
  unfold low outputLowStore lowMemory
  apply storeI64_memory
  rw[mems_paid];exact high_memory s op p hm
theorem tagged_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (tagged s op p).mems[p.index]?=some (tagMemory p):=by
  unfold tagged outputTagStore tagMemory
  apply storeI32_memory
  rw[mems_paid];exact low_memory s op p hm
theorem described_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (described s op p).mems[p.index]?=some (finalMemory p):=by
  unfold described StateDecodeScalar.store64Local finalMemory
  apply storeI64_memory
  rw[mems_paid];exact tagged_memory s op p hm

theorem cached_modules(s:Store NearState)(op:Nat):(cached s op).modules=s.modules:=by rw[cached,modules_paid]
theorem high_modules(s:Store NearState)(op:Nat)(p:Layout):(high s op p).modules=s.modules:=by
  simp only[high,outputHighStore,storeI32_modules,modules_paid,cached_modules]
theorem low_modules(s:Store NearState)(op:Nat)(p:Layout):(low s op p).modules=s.modules:=by
  simp only[low,outputLowStore,storeI64_modules,modules_paid,high_modules]
theorem tagged_modules(s:Store NearState)(op:Nat)(p:Layout):(tagged s op p).modules=s.modules:=by
  simp only[tagged,outputTagStore,storeI32_modules,modules_paid,low_modules]
end WNear.Proofs.StateDecodePrefix.Output
