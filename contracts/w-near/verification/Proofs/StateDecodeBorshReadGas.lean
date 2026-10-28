import Proofs.StateDecodeBorshReadPhases
import Proofs.StateDecodeBorshReadDomain
import Proofs.UnwrapStateCopyGas

/-! Exact gas and residual credits for all161 phases, including the actual162
child, three forward copies and the deployed descriptor stores. -/
namespace WNear.Proofs.StateDecodeBorshRead
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
private theorem wrapper_units(cfg:WasmConfig)(s:Store NearState)(p:StateDecodeBorshWrapper.Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:StateDecodeBorshWrapper.Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    GasUnits s (StateDecodeBorshWrapper.callAfter cfg s p q) cfg.regularOpCost (18*(StateDecodeBorshWrapper.count p).toNat+2847):=by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only[Nat.one_mul] at one
  have enter:GasUnits s (StateDecodeBorshWrapper.entered s cfg.regularOpCost) cfg.regularOpCost 12:=
    one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 11)
  have body:=StateDecodeBorshWrapper.after_gas cfg (StateDecodeBorshWrapper.entered s cfg.regularOpCost) p q hn hd
  simpa only[StateDecodeBorshWrapper.callAfter,show 12+(18*(StateDecodeBorshWrapper.count p).toNat+2835)=18*(StateDecodeBorshWrapper.count p).toNat+2847 by omega] using enter.trans body
attribute [local irreducible] scratch count wrappedMemory packedValue tagValue scratchMemory upperMemory acceptedMemory resultMemory finalMemory reserved highSaved sliceSaved wrapperArguments wrapped packedCached tagCached firstCopyArguments firstCopied firstDropped guarded upperSaved acceptedCopyArguments acceptedCopied acceptedDropped exhausted resultCopyArguments resultCopied resultDropped tagged branched after

theorem reserved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (reserved s cfg.regularOpCost p) cfg.regularOpCost 5:=by
  have c:=global_units s cfg.regularOpCost 5 p.globalIndex (.i32 (scratch p))
  unfold reserved
  exact c

theorem highSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (highSaved s cfg.regularOpCost p) cfg.regularOpCost 8:=by
  have h:=reserved_gas cfg s p
  have c:=store_units (reserved s cfg.regularOpCost p) cfg.regularOpCost 3 p.memoryIndex ((scratch p).toNat+12) p.memory p.length
  unfold highSaved
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show 5+3=8 by omega] using h.trans c

theorem sliceSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (sliceSaved s cfg.regularOpCost p) cfg.regularOpCost 11:=by
  have h:=highSaved_gas cfg s p
  have c:=store_units (highSaved s cfg.regularOpCost p) cfg.regularOpCost 3 p.memoryIndex ((scratch p).toNat+8) (highSetupMemory p) p.pointer
  unfold sliceSaved
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show 8+3=11 by omega] using h.trans c

theorem wrapperArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout):
    GasUnits s (wrapperArguments s cfg.regularOpCost p) cfg.regularOpCost 17:=by
  have h:=sliceSaved_gas cfg s p
  have c:=gasUnits_paid (sliceSaved s cfg.regularOpCost p) cfg.regularOpCost 6
  unfold wrapperArguments
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show 11+6=17 by omega] using h.trans c

theorem wrapped_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (wrapped cfg s p q) cfg.regularOpCost (18*(count p).toNat+2864):=by
  have h:=wrapperArguments_gas cfg s p
  have c:=wrapper_units cfg (wrapperArguments s cfg.regularOpCost p) (actualWrapper p) (actualAllocation p q) (wrapper_native p hn) (accepted_domain p q hn hd)
  rw[actual_count p hn] at c
  unfold wrapped
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show 17+(18*(count p).toNat+2847)=(18*(count p).toNat+2864) by omega] using h.trans c

theorem packedCached_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (packedCached cfg s p q) cfg.regularOpCost (18*(count p).toNat+2867):=by
  have h:=wrapped_gas cfg s p q hn hd
  have c:=gasUnits_paid (wrapped cfg s p q) cfg.regularOpCost 3
  unfold packedCached
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2864)+3=(18*(count p).toNat+2867) by omega] using h.trans c

theorem tagCached_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (tagCached cfg s p q) cfg.regularOpCost (18*(count p).toNat+2870):=by
  have h:=packedCached_gas cfg s p q hn hd
  have c:=gasUnits_paid (packedCached cfg s p q) cfg.regularOpCost 3
  unfold tagCached
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2867)+3=(18*(count p).toNat+2870) by omega] using h.trans c

theorem firstCopyArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (firstCopyArguments cfg s p q) cfg.regularOpCost (18*(count p).toNat+2877):=by
  have h:=tagCached_gas cfg s p q hn hd
  have c:=gasUnits_paid (tagCached cfg s p q) cfg.regularOpCost 7
  unfold firstCopyArguments
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2870)+7=(18*(count p).toNat+2877) by omega] using h.trans c

theorem firstCopied_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (firstCopied cfg s p q) cfg.regularOpCost (18*(count p).toNat+3542):=by
  have h:=firstCopyArguments_gas cfg s p q hn hd
  have c:=memcpy_units (firstCopyArguments cfg s p q) cfg.regularOpCost p.memoryIndex (scratch p+60) (scratch p+108) (wrappedMemory p q) 36 (by decide)
  unfold firstCopied
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+2877)+665=(18*(count p).toNat+3542) by omega] using h.trans c

theorem firstDropped_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (firstDropped cfg s p q) cfg.regularOpCost (18*(count p).toNat+3543):=by
  have h:=firstCopied_gas cfg s p q hn hd
  have c:=gasUnits_paid (firstCopied cfg s p q) cfg.regularOpCost 1
  unfold firstDropped
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+3542)+1=(18*(count p).toNat+3543) by omega] using h.trans c

theorem guarded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (guarded cfg s p q) cfg.regularOpCost (18*(count p).toNat+3547):=by
  have h:=firstDropped_gas cfg s p q hn hd
  have c:=gasUnits_paid (firstDropped cfg s p q) cfg.regularOpCost 4
  unfold guarded
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+3543)+4=(18*(count p).toNat+3547) by omega] using h.trans c

theorem upperSaved_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (upperSaved cfg s p q) cfg.regularOpCost (18*(count p).toNat+3552):=by
  have h:=guarded_gas cfg s p q hn hd
  have c:=store_units (guarded cfg s p q) cfg.regularOpCost 5 p.memoryIndex ((scratch p).toNat+16) (scratchMemory p q) (UInt32.ofNat ((packedValue p q>>>32).toNat))
  unfold upperSaved
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+3547)+5=(18*(count p).toNat+3552) by omega] using h.trans c

theorem acceptedCopyArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (acceptedCopyArguments cfg s p q) cfg.regularOpCost (18*(count p).toNat+3561):=by
  have h:=upperSaved_gas cfg s p q hn hd
  have c:=gasUnits_paid (upperSaved cfg s p q) cfg.regularOpCost 9
  unfold acceptedCopyArguments
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+3552)+9=(18*(count p).toNat+3561) by omega] using h.trans c

theorem acceptedCopied_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (acceptedCopied cfg s p q) cfg.regularOpCost (18*(count p).toNat+4226):=by
  have h:=acceptedCopyArguments_gas cfg s p q hn hd
  have c:=memcpy_units (acceptedCopyArguments cfg s p q) cfg.regularOpCost p.memoryIndex ((scratch p+16)|||4) (scratch p+60) (upperMemory p q) 36 (by decide)
  unfold acceptedCopied
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+3561)+665=(18*(count p).toNat+4226) by omega] using h.trans c

theorem acceptedDropped_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (acceptedDropped cfg s p q) cfg.regularOpCost (18*(count p).toNat+4227):=by
  have h:=acceptedCopied_gas cfg s p q hn hd
  have c:=gasUnits_paid (acceptedCopied cfg s p q) cfg.regularOpCost 1
  unfold acceptedDropped
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4226)+1=(18*(count p).toNat+4227) by omega] using h.trans c

theorem exhausted_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (exhausted cfg s p q) cfg.regularOpCost (18*(count p).toNat+4231):=by
  have h:=acceptedDropped_gas cfg s p q hn hd
  have c:=gasUnits_paid (acceptedDropped cfg s p q) cfg.regularOpCost 4
  unfold exhausted
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4227)+4=(18*(count p).toNat+4231) by omega] using h.trans c

theorem resultCopyArguments_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (resultCopyArguments cfg s p q) cfg.regularOpCost (18*(count p).toNat+4238):=by
  have h:=exhausted_gas cfg s p q hn hd
  have c:=gasUnits_paid (exhausted cfg s p q) cfg.regularOpCost 7
  unfold resultCopyArguments
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4231)+7=(18*(count p).toNat+4238) by omega] using h.trans c

theorem resultCopied_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (resultCopied cfg s p q) cfg.regularOpCost (18*(count p).toNat+4975):=by
  have h:=resultCopyArguments_gas cfg s p q hn hd
  have c:=memcpy_units (resultCopyArguments cfg s p q) cfg.regularOpCost p.memoryIndex (p.out161+8) (scratch p+16) (acceptedMemory p q) 40 (by decide)
  unfold resultCopied
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4238)+737=(18*(count p).toNat+4975) by omega] using h.trans c

theorem resultDropped_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (resultDropped cfg s p q) cfg.regularOpCost (18*(count p).toNat+4976):=by
  have h:=resultCopied_gas cfg s p q hn hd
  have c:=gasUnits_paid (resultCopied cfg s p q) cfg.regularOpCost 1
  unfold resultDropped
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4975)+1=(18*(count p).toNat+4976) by omega] using h.trans c

theorem tagged_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (tagged cfg s p q) cfg.regularOpCost (18*(count p).toNat+4979):=by
  have h:=resultDropped_gas cfg s p q hn hd
  have c:=store_units (resultDropped cfg s p q) cfg.regularOpCost 3 p.memoryIndex p.out161.toNat (resultMemory p q) 0
  unfold tagged
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4976)+3=(18*(count p).toNat+4979) by omega] using h.trans c

theorem branched_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (branched cfg s p q) cfg.regularOpCost (18*(count p).toNat+4980):=by
  have h:=tagged_gas cfg s p q hn hd
  have c:=gasUnits_charge (tagged cfg s p q) cfg.regularOpCost 1
  unfold branched
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4979)+1=(18*(count p).toNat+4980) by omega] using h.trans c

theorem after_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q):
    GasUnits s (after cfg s p q) cfg.regularOpCost (18*(count p).toNat+4984):=by
  have h:=branched_gas cfg s p q hn hd
  have c:=global_units (branched cfg s p q) cfg.regularOpCost 4 p.globalIndex (.i32 p.sp161)
  unfold after
  simpa only[Nat.one_mul,Nat.reduceMul,Nat.reduceAdd,show (18*(count p).toNat+4980)+4=(18*(count p).toNat+4984) by omega] using h.trans c

theorem reserved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest)):
    (reserved s cfg.regularOpCost p).host.gas.Credits rest:=(reserved_gas cfg s p rest hc).2.2

theorem highSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (8*cfg.regularOpCost+rest)):
    (highSaved s cfg.regularOpCost p).host.gas.Credits rest:=(highSaved_gas cfg s p rest hc).2.2

theorem sliceSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (11*cfg.regularOpCost+rest)):
    (sliceSaved s cfg.regularOpCost p).host.gas.Credits rest:=(sliceSaved_gas cfg s p rest hc).2.2

theorem wrapperArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (17*cfg.regularOpCost+rest)):
    (wrapperArguments s cfg.regularOpCost p).host.gas.Credits rest:=(wrapperArguments_gas cfg s p rest hc).2.2

theorem wrapped_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+2864)*cfg.regularOpCost+rest)):
    (wrapped cfg s p q).host.gas.Credits rest:=(wrapped_gas cfg s p q hn hd rest hc).2.2

theorem packedCached_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+2867)*cfg.regularOpCost+rest)):
    (packedCached cfg s p q).host.gas.Credits rest:=(packedCached_gas cfg s p q hn hd rest hc).2.2

theorem tagCached_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+2870)*cfg.regularOpCost+rest)):
    (tagCached cfg s p q).host.gas.Credits rest:=(tagCached_gas cfg s p q hn hd rest hc).2.2

theorem firstCopyArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+2877)*cfg.regularOpCost+rest)):
    (firstCopyArguments cfg s p q).host.gas.Credits rest:=(firstCopyArguments_gas cfg s p q hn hd rest hc).2.2

theorem firstCopied_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+3542)*cfg.regularOpCost+rest)):
    (firstCopied cfg s p q).host.gas.Credits rest:=(firstCopied_gas cfg s p q hn hd rest hc).2.2

theorem firstDropped_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+3543)*cfg.regularOpCost+rest)):
    (firstDropped cfg s p q).host.gas.Credits rest:=(firstDropped_gas cfg s p q hn hd rest hc).2.2

theorem guarded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+3547)*cfg.regularOpCost+rest)):
    (guarded cfg s p q).host.gas.Credits rest:=(guarded_gas cfg s p q hn hd rest hc).2.2

theorem upperSaved_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+3552)*cfg.regularOpCost+rest)):
    (upperSaved cfg s p q).host.gas.Credits rest:=(upperSaved_gas cfg s p q hn hd rest hc).2.2

theorem acceptedCopyArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+3561)*cfg.regularOpCost+rest)):
    (acceptedCopyArguments cfg s p q).host.gas.Credits rest:=(acceptedCopyArguments_gas cfg s p q hn hd rest hc).2.2

theorem acceptedCopied_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4226)*cfg.regularOpCost+rest)):
    (acceptedCopied cfg s p q).host.gas.Credits rest:=(acceptedCopied_gas cfg s p q hn hd rest hc).2.2

theorem acceptedDropped_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4227)*cfg.regularOpCost+rest)):
    (acceptedDropped cfg s p q).host.gas.Credits rest:=(acceptedDropped_gas cfg s p q hn hd rest hc).2.2

theorem exhausted_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4231)*cfg.regularOpCost+rest)):
    (exhausted cfg s p q).host.gas.Credits rest:=(exhausted_gas cfg s p q hn hd rest hc).2.2

theorem resultCopyArguments_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4238)*cfg.regularOpCost+rest)):
    (resultCopyArguments cfg s p q).host.gas.Credits rest:=(resultCopyArguments_gas cfg s p q hn hd rest hc).2.2

theorem resultCopied_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4975)*cfg.regularOpCost+rest)):
    (resultCopied cfg s p q).host.gas.Credits rest:=(resultCopied_gas cfg s p q hn hd rest hc).2.2

theorem resultDropped_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4976)*cfg.regularOpCost+rest)):
    (resultDropped cfg s p q).host.gas.Credits rest:=(resultDropped_gas cfg s p q hn hd rest hc).2.2

theorem tagged_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4979)*cfg.regularOpCost+rest)):
    (tagged cfg s p q).host.gas.Credits rest:=(tagged_gas cfg s p q hn hd rest hc).2.2

theorem branched_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4980)*cfg.regularOpCost+rest)):
    (branched cfg s p q).host.gas.Credits rest:=(branched_gas cfg s p q hn hd rest hc).2.2

theorem after_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4984)*cfg.regularOpCost+rest)):
    (after cfg s p q).host.gas.Credits rest:=(after_gas cfg s p q hn hd rest hc).2.2
end WNear.Proofs.StateDecodeBorshRead
