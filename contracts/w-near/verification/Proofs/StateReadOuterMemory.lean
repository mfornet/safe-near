import Proofs.StateReadOuterDomain
import Proofs.StateReadOuterReleaseCode
import Proofs.StateDecodeBorshReadResult
import Proofs.UnwrapStateCopyEffects

/-! Memory endpoints after219's complete storage call. Intermediate lookup
inputs here are provided by the preceding phase, never execution outcomes. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem charged_mems(s:Store NearState)(op:Nat):(chargedStore s op).mems=s.mems:=rfl
private theorem copies_memory(s:Store NearState)(op i:Nat)(m:Memory)(r:UInt32)
    (hm:s.mems[i]?=some m):
    (copiedStorage s op i m r).mems[i]?=some (copiedStorageMemory m r):=by
  have high:(storageHighStore s op i m r).mems[i]?=some (storageHighMemory m r):=by
    unfold storageHighStore storageHighMemory
    apply storeI32_memory
    rw[paid_mems];exact hm
  unfold copiedStorage copiedStorageMemory storageLowStore storageLowMemory
  apply storeI64_memory
  rw[paid_mems];exact high
private theorem pack_composition(p:Layout):
    PackWords.packedMemory (copiedMemory p) (scratch p).toNat (scratch p+24).toNat=packedMemory p:=rfl
attribute [local irreducible] storageMemory copiedMemory packedMemory decodedMemory outputMemory finalMemory
attribute [local irreducible] stored presenceChecked storageCopied packArguments packed decodeArguments decoded decodeGuarded copyArguments outputCopied outputDropped releaseArguments released restored after

theorem presenceChecked_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (presenceChecked cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p):=by
  rw[presenceChecked,paid_mems];exact hm

theorem storageCopied_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (storageCopied cfg s p ctx key).mems[p.memoryIndex]?=some (copiedMemory p):=by
  have before:=presenceChecked_memory cfg s p ctx key hm
  rw[storageCopied]
  simpa only[copiedMemory] using copies_memory _ _ _ _ _ before

theorem packArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (packArguments cfg s p ctx key).mems[p.memoryIndex]?=some (copiedMemory p):=by
  have before:=storageCopied_memory cfg s p ctx key hm
  rw[packArguments,paid_mems];exact before

theorem packed_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (packed cfg s p ctx key).mems[p.memoryIndex]?=some (packedMemory p):=by
  have before:=packArguments_memory cfg s p ctx key hm
  rw[packed]
  have result:=PackWordsCall.callAfter_memory (packArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex (scratch p) (scratch p+24) (copiedMemory p) before
  rw[pack_composition] at result
  exact result

theorem decodeArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (decodeArguments cfg s p ctx key).mems[p.memoryIndex]?=some (packedMemory p):=by
  have before:=packed_memory cfg s p ctx key hm
  rw[decodeArguments,paid_mems];exact before

theorem decoded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (decoded cfg s p ctx key).mems[p.memoryIndex]?=some (decodedMemory p):=by
  have before:=decodeArguments_memory cfg s p ctx key hm
  have input:(decodeArguments cfg s p ctx key).mems[(actualDecoder p).memoryIndex]?=some (actualDecoder p).memory:=by
    change (decodeArguments cfg s p ctx key).mems[p.decoderTemplate.memoryIndex]?=some (packedMemory p)
    rw[hn.decoderMemoryIndex];exact before
  have result:=StateDecodeBorshRead.callAfter_memory cfg (decodeArguments cfg s p ctx key) (actualDecoder p) (actualAllocation p)
    (decoder_native p hn state hw hb) (decoder_domain p hn state hw hb) input
  have index:(actualDecoder p).memoryIndex=p.memoryIndex:=hn.decoderMemoryIndex
  rw[index] at result
  simpa only[decoded,decodedMemory] using result

theorem decodeGuarded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (decodeGuarded cfg s p ctx key).mems[p.memoryIndex]?=some (decodedMemory p):=by
  have before:=decoded_memory cfg s p ctx key hn state hw hb hm
  rw[decodeGuarded,paid_mems];exact before

theorem copyArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (copyArguments cfg s p ctx key).mems[p.memoryIndex]?=some (decodedMemory p):=by
  have before:=decodeGuarded_memory cfg s p ctx key hn state hw hb hm
  rw[copyArguments,paid_mems];exact before

theorem outputCopied_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (outputCopied cfg s p ctx key).mems[p.memoryIndex]?=some (outputMemory p):=by
  have before:=copyArguments_memory cfg s p ctx key hn state hw hb hm
  rw[outputCopied]
  have native:=decoder_native p hn state hw hb
  have shape:=StateDecodeBorshRead.finalMemory_spec (actualDecoder p) (actualAllocation p) native (decoder_domain p hn state hw hb)
  have shapes:(decodedMemory p).wf ∧(decodedMemory p).byteSize=(packedMemory p).byteSize:=by
    simpa only[decodedMemory,actualDecoder_memory] using And.intro shape.1 shape.2.1
  have grow:=storage_grows p hn
  have packedShape:=packed_shape p hn
  have nums:=scratch_numbers p hn
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=by
    simpa only[show UInt32.ofNat 48=48 by rfl] using scratch_add p hn 48 (by omega)
  have source:(scratch p+48).toNat+40≤(decodedMemory p).byteSize:=by rw[a48,shapes.2,packedShape.2.1];omega
  have out:p.out219.toNat+40≤(decodedMemory p).byteSize:=by
    rw[shapes.2,packedShape.2.1];have bound:=hn.outputBound;omega
  have width:(decodedMemory p).byteSize≤2^32:=by rw[shapes.2];exact native.width
  have result:=UnwrapStateCopyEffects.callAfter_memory (copyArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex p.out219 (scratch p+48) (decodedMemory p) 40 before shapes.1 width source out
  simpa only[outputMemory] using result

theorem outputDropped_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (outputDropped cfg s p ctx key).mems[p.memoryIndex]?=some (outputMemory p):=by
  have before:=outputCopied_memory cfg s p ctx key hn state hw hb hm
  rw[outputDropped,paid_mems];exact before

theorem releaseArguments_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p)):
    (releaseArguments cfg s p ctx key).mems[p.memoryIndex]?=some (outputMemory p):=by
  have before:=outputDropped_memory cfg s p ctx key hn state hw hb hm
  rw[releaseArguments,paid_mems];exact before

theorem released_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p))(inst extra a581 a236:Nat)(hc:Code s inst p extra a581 a236):
    (released cfg s p ctx key).mems[p.memoryIndex]?=some (finalMemory p):=by
  have before:=releaseArguments_memory cfg s p ctx key hn state hw hb hm
  have index:(actualRelease p).memoryIndex=p.memoryIndex:=hc.release_memoryIndex s inst p extra a581 a236
  have input:(releaseArguments cfg s p ctx key).mems[(actualRelease p).memoryIndex]?=some (actualRelease p).memory:=by
    rw[index,actualRelease_memory];exact before
  have result:=VectorDropInsert.callAfter_memory (releaseArguments cfg s p ctx key) cfg.regularOpCost (actualRelease p) input
  rw[index] at result
  simpa only[released,finalMemory] using result

theorem restored_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p))(inst extra a581 a236:Nat)(hc:Code s inst p extra a581 a236):
    (restored cfg s p ctx key).mems[p.memoryIndex]?=some (finalMemory p):=by
  have before:=released_memory cfg s p ctx key hn state hw hb hm inst extra a581 a236 hc
  rw[restored,global_mems,paid_mems];exact before

theorem after_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8)(hn:Native p)(state:WNear.State)(hw:state.WF)(hb:p.bytes=WNear.header state)(hm:(stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p))(inst extra a581 a236:Nat)(hc:Code s inst p extra a581 a236):
    (after cfg s p ctx key).mems[p.memoryIndex]?=some (finalMemory p):=by
  have before:=restored_memory cfg s p ctx key hn state hw hb hm inst extra a581 a236 hc
  rw[after,charged_mems];exact before
end WNear.Proofs.StateReadOuter
