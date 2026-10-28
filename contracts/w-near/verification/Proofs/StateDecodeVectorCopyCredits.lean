import Proofs.StateDecodeVectorCopySuffix

namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] UnwrapStateCopyEntry.callAfter StateDecodeVector.callAfter

theorem finishStore_credits (s:Store NearState)(op index rest:Nat)(memory:Memory)(out size:UInt32)
    (hc:s.host.gas.Credits (4*op+rest)):(finishStore s op index memory out size).host.gas.Credits rest:=by
  simpa only[finishStore,storeI32_host] using paid_credits s op 4 rest hc

theorem suffixAfter_credits (s:Store NearState)(op index rest:Nat)(memory:Memory)(out source size:UInt32)
    (hp:0<size.toNat)(hc:s.host.gas.Credits ((18*size.toNat+25)*op+rest)):
    (suffixAfter s op index memory out source size).host.gas.Credits rest:=by
  have c4:=paid_credits s op 4 ((18*size.toNat+17)*op+(4*op+rest)) (hc.mono (by simp only[Nat.add_mul];omega))
  have cc:=UnwrapStateCopyEntry.callAfter_credits (paid s op 4) op index (readI32 memory out.toNat) source memory size.toNat (4*op+rest) hp c4
  exact finishStore_credits _ op index rest _ out size cc

theorem after_credits (cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)(hn:Native p)
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest)):
    (after cfg s p).host.gas.Credits rest:=by
  let op:=cfg.regularOpCost
  let cost:=(18*p.size.toNat+25)*op+rest
  have c2:(vectorBefore s op).host.gas.Credits (620*op+cost):=paid_credits s op 2 _ (hc.mono (by dsimp[bodyCost,cost,op];simp only[Nat.add_mul];omega))
  have cv: (vectorAfter cfg s p).host.gas.Credits cost:=StateDecodeVector.callAfter_credits cfg (vectorBefore s op) p.toVector cost c2
  have hp:0<p.size.toNat:=(copy_bounds p hn).2.2.2.2.2.1
  have ptr:=StateDecodeVector.finalMemory_pointer p.toVector hn.vector
  have suffixEq:after cfg s p=suffixAfter (vectorAfter cfg s p) op p.memoryIndex (StateDecodeVector.finalMemory p.toVector) p.outVector p.source p.size:=by
    simp only[after,suffixAfter,copied,copyArguments,copiedMemory,ptr,pointer,op]
  rw[suffixEq]
  exact suffixAfter_credits (vectorAfter cfg s p) op p.memoryIndex rest (StateDecodeVector.finalMemory p.toVector) p.outVector p.source p.size hp cv
end WNear.Proofs.StateDecodeVectorCopy
