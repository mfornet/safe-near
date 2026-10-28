import Proofs.StateReadOuterDomain
import Proofs.StateDecodeBorshReadResult
import Proofs.UnwrapStateCopyGas

/-! Exact ordinary gas and residual credits after219's storage548 call.
The storage/register/growth fees are accounted for by548, once. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
attribute [local irreducible] packedMemory decodedMemory outputMemory actualRelease decodeCount actualDecoder actualAllocation
private theorem word_units(s:Store NearState)(op n i a:Nat)(m:Memory)(v:UInt32):
    GasUnits s (storeI32 (paid s op n) i a m v) op n:=(gasUnits_paid s op n).host_eq rfl
private theorem wide_units(s:Store NearState)(op n i a:Nat)(m:Memory)(v:UInt64):
    GasUnits s (storeI64 (paid s op n) i a m v) op n:=(gasUnits_paid s op n).host_eq rfl
private theorem copy_storage_units(s:Store NearState)(op i:Nat)(m:Memory)(r:UInt32):
    GasUnits s (copiedStorage s op i m r) op 16:=by
  have hi:=word_units s op 12 i ((r+24)+8).toNat m (readI32 m ((r+8)+8).toNat)
  have lo:=wide_units (storageHighStore s op i m r) op 4 i (r.toNat+24) (storageHighMemory m r) (readI64 (storageHighMemory m r) (r.toNat+8))
  simpa only[copiedStorage,storageHighStore,storageLowStore,Nat.reduceAdd] using hi.trans lo
private theorem packed_units(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory):
    GasUnits s (PackWordsCall.callAfter s op i out src m) op 18:=by
  intro rest hc
  exact PackWordsCall.callAfter_gas s op i out src m rest hc
private theorem memcpy_units(s:Store NearState)(op i:Nat)(out src:UInt32)(m:Memory):
    GasUnits s (UnwrapStateCopyEntry.callAfter s op i out src m 40) op 737:=by
  have one:=gasUnits_charge s op 1
  simp only[Nat.one_mul] at one
  have enter:GasUnits s (UnwrapStateCopyEntry.calledStore s op) op 11:=
    one.trans (gasUnits_charge (chargedStore s op) op 10)
  have prep:GasUnits (UnwrapStateCopyEntry.calledStore s op)
      (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op 6:=by
    simpa only[UnwrapStateCopyEntry.prepared,Nat.reduceAdd,Nat.one_mul] using
      (gasUnits_paid (UnwrapStateCopyEntry.calledStore s op) op 5).trans
        (gasUnits_charge (paid (UnwrapStateCopyEntry.calledStore s op) op 5) op 1)
  have loop:GasUnits (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op)
      (UnwrapStateCopy.loopStore (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op i out src m 40) op 719:=by
    intro rest hc
    have gas:=UnwrapStateCopyGas.loopStore_gas _ op i out src m 40 rest hc
    exact ⟨gas.1,gas.2,UnwrapStateCopyState.loopStore_credits _ op i out src m 40 rest hc⟩
  have ret:=gasUnits_charge (UnwrapStateCopy.loopStore (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op i out src m 40) op 1
  simpa only[UnwrapStateCopyEntry.callAfter,UnwrapStateCopyEntry.finalStore,Nat.one_mul,Nat.reduceAdd] using ((enter.trans prep).trans loop).trans ret
attribute [local irreducible] stored presenceChecked storageCopied packArguments packed decodeArguments decoded decodeGuarded copyArguments outputCopied outputDropped releaseArguments released restored after

theorem presenceChecked_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    GasUnits (stored cfg s p ctx key) (presenceChecked cfg s p ctx key) cfg.regularOpCost (3):=by
  have step:=gasUnits_paid (stored cfg s p ctx key) cfg.regularOpCost 3
  simpa only[presenceChecked] using step

theorem presenceChecked_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((3)*cfg.regularOpCost+rest)):
    (presenceChecked cfg s p ctx key).host.gas.Credits rest:=(presenceChecked_post_storage_gas cfg s p ctx key rest hc).2.2

theorem storageCopied_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    GasUnits (stored cfg s p ctx key) (storageCopied cfg s p ctx key) cfg.regularOpCost (19):=by
  have step:=copy_storage_units (presenceChecked cfg s p ctx key) cfg.regularOpCost p.memoryIndex (storageMemory p) (scratch p)
  have before:=presenceChecked_post_storage_gas cfg s p ctx key
  have result:=before.trans step
  simpa only[storageCopied,Nat.one_mul,Nat.reduceAdd,show (3)+(16)=(19) by omega] using result

theorem storageCopied_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((19)*cfg.regularOpCost+rest)):
    (storageCopied cfg s p ctx key).host.gas.Credits rest:=(storageCopied_post_storage_gas cfg s p ctx key rest hc).2.2

theorem packArguments_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    GasUnits (stored cfg s p ctx key) (packArguments cfg s p ctx key) cfg.regularOpCost (23):=by
  have step:=gasUnits_paid (storageCopied cfg s p ctx key) cfg.regularOpCost 4
  have before:=storageCopied_post_storage_gas cfg s p ctx key
  have result:=before.trans step
  simpa only[packArguments,Nat.one_mul,Nat.reduceAdd,show (19)+(4)=(23) by omega] using result

theorem packArguments_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((23)*cfg.regularOpCost+rest)):
    (packArguments cfg s p ctx key).host.gas.Credits rest:=(packArguments_post_storage_gas cfg s p ctx key rest hc).2.2

theorem packed_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    GasUnits (stored cfg s p ctx key) (packed cfg s p ctx key) cfg.regularOpCost (41):=by
  have step:=packed_units (packArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex (scratch p) (scratch p+24) (copiedMemory p)
  have before:=packArguments_post_storage_gas cfg s p ctx key
  have result:=before.trans step
  simpa only[packed,Nat.one_mul,Nat.reduceAdd,show (23)+(18)=(41) by omega] using result

theorem packed_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((41)*cfg.regularOpCost+rest)):
    (packed cfg s p ctx key).host.gas.Credits rest:=(packed_post_storage_gas cfg s p ctx key rest hc).2.2

theorem decodeArguments_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):
    GasUnits (stored cfg s p ctx key) (decodeArguments cfg s p ctx key) cfg.regularOpCost (48):=by
  have step:=gasUnits_paid (packed cfg s p ctx key) cfg.regularOpCost 7
  have before:=packed_post_storage_gas cfg s p ctx key
  have result:=before.trans step
  simpa only[decodeArguments,Nat.one_mul,Nat.reduceAdd,show (41)+(7)=(48) by omega] using result

theorem decodeArguments_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((48)*cfg.regularOpCost+rest)):
    (decodeArguments cfg s p ctx key).host.gas.Credits rest:=(decodeArguments_post_storage_gas cfg s p ctx key rest hc).2.2

theorem decoded_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (decoded cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+5044):=by
  have step:=StateDecodeBorshRead.callAfter_gas cfg (decodeArguments cfg s p ctx key) (actualDecoder p) (actualAllocation p) (decoder_native p hn state hw hb) (decoder_domain p hn state hw hb)
  have countEq:StateDecodeBorshRead.count (actualDecoder p)=decodeCount p:=by unfold decodeCount;rfl
  rw[countEq] at step
  have before:=decodeArguments_post_storage_gas cfg s p ctx key
  have result:=before.trans step
  simpa only[decoded,Nat.one_mul,Nat.reduceAdd,show (48)+(18*(decodeCount p).toNat+4996)=(18*(decodeCount p).toNat+5044) by omega] using result

theorem decoded_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+5044)*cfg.regularOpCost+rest)):
    (decoded cfg s p ctx key).host.gas.Credits rest:=(decoded_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem decodeGuarded_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (decodeGuarded cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+5049):=by
  have step:=gasUnits_paid (decoded cfg s p ctx key) cfg.regularOpCost 5
  have before:=decoded_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[decodeGuarded,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+5044)+(5)=(18*(decodeCount p).toNat+5049) by omega] using result

theorem decodeGuarded_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+5049)*cfg.regularOpCost+rest)):
    (decodeGuarded cfg s p ctx key).host.gas.Credits rest:=(decodeGuarded_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem copyArguments_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (copyArguments cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+5056):=by
  have step:=gasUnits_paid (decodeGuarded cfg s p ctx key) cfg.regularOpCost 7
  have before:=decodeGuarded_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[copyArguments,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+5049)+(7)=(18*(decodeCount p).toNat+5056) by omega] using result

theorem copyArguments_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+5056)*cfg.regularOpCost+rest)):
    (copyArguments cfg s p ctx key).host.gas.Credits rest:=(copyArguments_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem outputCopied_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (outputCopied cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+5793):=by
  have step:=memcpy_units (copyArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex p.out219 (scratch p+48) (decodedMemory p)
  have before:=copyArguments_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[outputCopied,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+5056)+(737)=(18*(decodeCount p).toNat+5793) by omega] using result

theorem outputCopied_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+5793)*cfg.regularOpCost+rest)):
    (outputCopied cfg s p ctx key).host.gas.Credits rest:=(outputCopied_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem outputDropped_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (outputDropped cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+5794):=by
  have step:=gasUnits_paid (outputCopied cfg s p ctx key) cfg.regularOpCost 1
  have before:=outputCopied_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[outputDropped,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+5793)+(1)=(18*(decodeCount p).toNat+5794) by omega] using result

theorem outputDropped_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+5794)*cfg.regularOpCost+rest)):
    (outputDropped cfg s p ctx key).host.gas.Credits rest:=(outputDropped_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem releaseArguments_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (releaseArguments cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+5797):=by
  have step:=gasUnits_paid (outputDropped cfg s p ctx key) cfg.regularOpCost 3
  have before:=outputDropped_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[releaseArguments,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+5794)+(3)=(18*(decodeCount p).toNat+5797) by omega] using result

theorem releaseArguments_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+5797)*cfg.regularOpCost+rest)):
    (releaseArguments cfg s p ctx key).host.gas.Credits rest:=(releaseArguments_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem released_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (released cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+6027):=by
  have step:=VectorDropInsert.callAfter_gas (releaseArguments cfg s p ctx key) cfg.regularOpCost (actualRelease p)
  have before:=releaseArguments_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[released,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+5797)+(230)=(18*(decodeCount p).toNat+6027) by omega] using result

theorem released_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+6027)*cfg.regularOpCost+rest)):
    (released cfg s p ctx key).host.gas.Credits rest:=(released_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem restored_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (restored cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+6031):=by
  have step:=(gasUnits_paid (released cfg s p ctx key) cfg.regularOpCost 4).host_eq (show (setGlobal (paid (released cfg s p ctx key) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp219)).host=(paid (released cfg s p ctx key) cfg.regularOpCost 4).host by rfl)
  have before:=released_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[restored,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+6027)+(4)=(18*(decodeCount p).toNat+6031) by omega] using result

theorem restored_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+6031)*cfg.regularOpCost+rest)):
    (restored cfg s p ctx key).host.gas.Credits rest:=(restored_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2

theorem after_post_storage_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state):
    GasUnits (stored cfg s p ctx key) (after cfg s p ctx key) cfg.regularOpCost (18*(decodeCount p).toNat+6032):=by
  have step:=gasUnits_charge (restored cfg s p ctx key) cfg.regularOpCost 1
  have before:=restored_post_storage_gas cfg s p ctx key hn state hw hb
  have result:=before.trans step
  simpa only[after,Nat.one_mul,Nat.reduceAdd,show (18*(decodeCount p).toNat+6031)+(1)=(18*(decodeCount p).toNat+6032) by omega] using result

theorem after_post_storage_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(rest:Nat)
    (hc:(stored cfg s p ctx key).host.gas.Credits ((18*(decodeCount p).toNat+6032)*cfg.regularOpCost+rest)):
    (after cfg s p ctx key).host.gas.Credits rest:=(after_post_storage_gas cfg s p ctx key hn state hw hb rest hc).2.2
end WNear.Proofs.StateReadOuter
