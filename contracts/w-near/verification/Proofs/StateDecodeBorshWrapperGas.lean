import Proofs.StateDecodeBorshWrapperState
import Proofs.UnwrapStateCopyGas

/-! Every actual162 phase's exact gas and residual credits, including both
complete36-byte951 calls and the real packed store. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
private theorem loop_units (s : Store NearState) (op i : Nat) (out src : UInt32) (m : Memory) (n : Nat) :
    GasUnits s (UnwrapStateCopy.loopStore s op i out src m n) op (18*n-1) := by
  intro rest hc
  have gas:=UnwrapStateCopyGas.loopStore_gas s op i out src m n rest hc
  exact ⟨gas.1,gas.2,UnwrapStateCopyState.loopStore_credits s op i out src m n rest hc⟩
private theorem memcpy_units (s : Store NearState) (op i : Nat) (out src : UInt32) (m : Memory) (n : Nat) (hn : 0<n) :
    GasUnits s (UnwrapStateCopyEntry.callAfter s op i out src m n) op (18*n+17) := by
  have one:=gasUnits_charge s op 1
  simp only [Nat.one_mul] at one
  have enter : GasUnits s (UnwrapStateCopyEntry.calledStore s op) op 11 :=
    one.trans (gasUnits_charge (chargedStore s op) op 10)
  have prep : GasUnits (UnwrapStateCopyEntry.calledStore s op) (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op 6 := by
    simpa only [UnwrapStateCopyEntry.prepared,Nat.reduceAdd,Nat.one_mul] using
      (gasUnits_paid (UnwrapStateCopyEntry.calledStore s op) op 5).trans (gasUnits_charge (paid (UnwrapStateCopyEntry.calledStore s op) op 5) op 1)
  have loop:=loop_units (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op i out src m n
  have ret:=gasUnits_charge (UnwrapStateCopy.loopStore (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op i out src m n) op 1
  have ledger : 11+6+(18*n-1)+1=18*n+17 := by omega
  simpa only [UnwrapStateCopyEntry.callAfter,UnwrapStateCopyEntry.finalStore,Nat.one_mul,ledger] using ((enter.trans prep).trans loop).trans ret
private theorem global_units(s:Store NearState)(op n i:Nat)(v:Value):
    GasUnits s (setGlobal (paid s op n) i v) op n:=(gasUnits_paid s op n).host_eq rfl
private theorem store_units(s:Store NearState)(op n i a:Nat)(m:Memory)(v:UInt32):
    GasUnits s (storeI32 (paid s op n) i a m v) op n:=(gasUnits_paid s op n).host_eq rfl
attribute [local irreducible] scratch count decodedMemory packedValue tagValue firstMemory packedMemory secondMemory finalMemory reserved arguments decoded packedCached tagCached copyArguments copied guarded packedSaved outputArguments outputCopied accepted tagged after reservedFrame packedFrame tagFrame guardedFrame finalFrame bodyCost bodySteps

theorem reserved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (reserved s cfg.regularOpCost p) cfg.regularOpCost 5:=by
  unfold reserved
  exact global_units s cfg.regularOpCost 5 p.globalIndex (.i32 (scratch p))

theorem arguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (arguments s cfg.regularOpCost p) cfg.regularOpCost 9:=by
  have h:=reserved_gas cfg s p
  have c:=gasUnits_paid (reserved s cfg.regularOpCost p) cfg.regularOpCost 4
  unfold arguments
  simpa only[Nat.reduceMul,Nat.reduceAdd,show 5+4=9 by omega] using h.trans c

theorem decoded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (decoded cfg s p q) cfg.regularOpCost (18*(count p).toNat+1458):=by
  have h:=arguments_gas cfg s p
  have c:=StateDecodeBorsh.callAfter_gas cfg (arguments s cfg.regularOpCost p) p.toBorsh q hn.child hd
  have eq:StateDecodeBorsh.count p.toBorsh=count p:=by unfold count;rfl
  rw[eq] at c
  unfold decoded
  simpa only[Nat.reduceMul,Nat.reduceAdd,show 9+(18*(count p).toNat+1449)=18*(count p).toNat+1458 by omega] using h.trans c

theorem packedCached_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (packedCached cfg s p q) cfg.regularOpCost (18*(count p).toNat+1461):=by
  have h:=decoded_gas cfg s p q hn hd
  have c:=gasUnits_paid (decoded cfg s p q) cfg.regularOpCost 3
  unfold packedCached
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+1458)+3=18*(count p).toNat+1461 by omega] using h.trans c

theorem tagCached_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (tagCached cfg s p q) cfg.regularOpCost (18*(count p).toNat+1464):=by
  have h:=packedCached_gas cfg s p q hn hd
  have c:=gasUnits_paid (packedCached cfg s p q) cfg.regularOpCost 3
  unfold tagCached
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+1461)+3=18*(count p).toNat+1464 by omega] using h.trans c

theorem copyArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (copyArguments cfg s p q) cfg.regularOpCost (18*(count p).toNat+1473):=by
  have h:=tagCached_gas cfg s p q hn hd
  have c:=gasUnits_paid (tagCached cfg s p q) cfg.regularOpCost 9
  unfold copyArguments
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+1464)+9=18*(count p).toNat+1473 by omega] using h.trans c

theorem copied_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (copied cfg s p q) cfg.regularOpCost (18*(count p).toNat+2138):=by
  have h:=copyArguments_gas cfg s p q hn hd
  have c:=memcpy_units (copyArguments cfg s p q) cfg.regularOpCost p.memoryIndex (scratch p+12) ((scratch p+48)+12) (decodedMemory p q) 36 (by decide)
  unfold copied
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+1473)+665=18*(count p).toNat+2138 by omega] using h.trans c

theorem guarded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (guarded cfg s p q) cfg.regularOpCost (18*(count p).toNat+2145):=by
  have h:=copied_gas cfg s p q hn hd
  have c:=gasUnits_paid (copied cfg s p q) cfg.regularOpCost 7
  unfold guarded
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2138)+7=18*(count p).toNat+2145 by omega] using h.trans c

theorem packedSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (packedSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+2152):=by
  have h:=guarded_gas cfg s p q hn hd
  have c:=store_units (guarded cfg s p q) cfg.regularOpCost 7 p.memoryIndex (p.out162+8).toNat (firstMemory p q) (UInt32.ofNat ((packedValue p q >>>32).toNat))
  unfold packedSaved
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2145)+7=18*(count p).toNat+2152 by omega] using h.trans c

theorem outputArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (outputArguments cfg s p q) cfg.regularOpCost (18*(count p).toNat+2159):=by
  have h:=packedSaved_gas cfg s p q hn hd
  have c:=gasUnits_paid (packedSaved cfg s p q) cfg.regularOpCost 7
  unfold outputArguments
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2152)+7=18*(count p).toNat+2159 by omega] using h.trans c

theorem outputCopied_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (outputCopied cfg s p q) cfg.regularOpCost (18*(count p).toNat+2824):=by
  have h:=outputArguments_gas cfg s p q hn hd
  have c:=memcpy_units (outputArguments cfg s p q) cfg.regularOpCost p.memoryIndex (p.out162+12) (scratch p+12) (packedMemory p q) 36 (by decide)
  unfold outputCopied
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2159)+665=18*(count p).toNat+2824 by omega] using h.trans c

theorem accepted_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (accepted cfg s p q) cfg.regularOpCost (18*(count p).toNat+2828):=by
  have h:=outputCopied_gas cfg s p q hn hd
  have c:=gasUnits_paid (outputCopied cfg s p q) cfg.regularOpCost 4
  unfold accepted
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2824)+4=18*(count p).toNat+2828 by omega] using h.trans c

theorem tagged_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (tagged cfg s p q) cfg.regularOpCost (18*(count p).toNat+2831):=by
  have h:=accepted_gas cfg s p q hn hd
  have c:=store_units (accepted cfg s p q) cfg.regularOpCost 3 p.memoryIndex p.out162.toNat (secondMemory p q) 0
  unfold tagged
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2828)+3=18*(count p).toNat+2831 by omega] using h.trans c

theorem after_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (after cfg s p q) cfg.regularOpCost (18*(count p).toNat+2835):=by
  have h:=tagged_gas cfg s p q hn hd
  have c:=global_units (tagged cfg s p q) cfg.regularOpCost 4 p.globalIndex (.i32 p.sp162)
  unfold after
  simpa only[Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2831)+4=18*(count p).toNat+2835 by omega] using h.trans c

theorem reserved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)(hc:s.host.gas.Credits (5*cfg.regularOpCost+rest)):
    (reserved s cfg.regularOpCost p).host.gas.Credits rest:=(reserved_gas cfg s p rest hc).2.2

theorem arguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)(hc:s.host.gas.Credits (9*cfg.regularOpCost+rest)):
    (arguments s cfg.regularOpCost p).host.gas.Credits rest:=(arguments_gas cfg s p rest hc).2.2

theorem decoded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+1458)*cfg.regularOpCost+rest)):
    (decoded cfg s p q).host.gas.Credits rest:=(decoded_gas cfg s p q hn hd rest hc).2.2

theorem packedCached_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+1461)*cfg.regularOpCost+rest)):
    (packedCached cfg s p q).host.gas.Credits rest:=(packedCached_gas cfg s p q hn hd rest hc).2.2

theorem tagCached_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+1464)*cfg.regularOpCost+rest)):
    (tagCached cfg s p q).host.gas.Credits rest:=(tagCached_gas cfg s p q hn hd rest hc).2.2

theorem copyArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+1473)*cfg.regularOpCost+rest)):
    (copyArguments cfg s p q).host.gas.Credits rest:=(copyArguments_gas cfg s p q hn hd rest hc).2.2

theorem copied_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2138)*cfg.regularOpCost+rest)):
    (copied cfg s p q).host.gas.Credits rest:=(copied_gas cfg s p q hn hd rest hc).2.2

theorem guarded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2145)*cfg.regularOpCost+rest)):
    (guarded cfg s p q).host.gas.Credits rest:=(guarded_gas cfg s p q hn hd rest hc).2.2

theorem packedSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2152)*cfg.regularOpCost+rest)):
    (packedSaved cfg s p q).host.gas.Credits rest:=(packedSaved_gas cfg s p q hn hd rest hc).2.2

theorem outputArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2159)*cfg.regularOpCost+rest)):
    (outputArguments cfg s p q).host.gas.Credits rest:=(outputArguments_gas cfg s p q hn hd rest hc).2.2

theorem outputCopied_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2824)*cfg.regularOpCost+rest)):
    (outputCopied cfg s p q).host.gas.Credits rest:=(outputCopied_gas cfg s p q hn hd rest hc).2.2

theorem accepted_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2828)*cfg.regularOpCost+rest)):
    (accepted cfg s p q).host.gas.Credits rest:=(accepted_gas cfg s p q hn hd rest hc).2.2

theorem tagged_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2831)*cfg.regularOpCost+rest)):
    (tagged cfg s p q).host.gas.Credits rest:=(tagged_gas cfg s p q hn hd rest hc).2.2

theorem after_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(rest:Nat)(hc:s.host.gas.Credits ((18*(count p).toNat+2835)*cfg.regularOpCost+rest)):
    (after cfg s p q).host.gas.Credits rest:=(after_gas cfg s p q hn hd rest hc).2.2
end WNear.Proofs.StateDecodeBorshWrapper
