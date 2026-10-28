import Proofs.StateReadOuterState
import Proofs.StateReadStorageOuterCode
import Proofs.StateDecodeBorshReadCode
import Proofs.DeallocateCoreFrame

/-! Original installed descriptors of219. The allocation template may describe
an initially empty heap: no allocator Native or future child Code is assumed. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic

structure Code(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat):Prop where
  storage:StateReadStorageOuter.Code s inst p.toStorage extra
  decoder:StateDecodeBorshRead.Code s inst p.decoderTemplate p.allocationTemplate a581 a236
  release:DeallocateCore.Code s inst p.releaseTemplate
  vectorModule:s.modules[inst]?=some p.vectorTemplate.mi
  vectorMemoryIndex:p.vectorTemplate.mi.memAddrs[0]?=some p.vectorTemplate.memoryIndex
  index778:p.vectorTemplate.mi.funcAddrs[778]?=some p.vectorTemplate.address778
  function778:s.funcs[p.vectorTemplate.address778]?=some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function778)
  index747:p.vectorTemplate.mi.funcAddrs[747]?=some p.vectorTemplate.address747
  function747:s.funcs[p.vectorTemplate.address747]?=some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function747)
  index777:p.vectorTemplate.mi.funcAddrs[777]?=some p.vectorTemplate.address777
  function777:s.funcs[p.vectorTemplate.address777]?=some (.wasm WNear.Binary.VectorDrop.tripleSignature inst WNear.Binary.VectorDrop.function777)
  index311:p.vectorTemplate.mi.funcAddrs[311]?=some p.vectorTemplate.address311
  function311:s.funcs[p.vectorTemplate.address311]?=some (.wasm WNear.Binary.VectorDrop.tripleSignature inst WNear.Binary.VectorDrop.function311)
  index548:p.mi.funcAddrs[548]?=some p.address548
  function548:s.funcs[p.address548]?=some (.wasm WNear.Binary.StateReadStorageOuter.signature inst WNear.Binary.StateReadStorageOuter.function)
  index779:p.mi.funcAddrs[779]?=some p.address779
  function779:s.funcs[p.address779]?=some (.wasm WNear.Binary.PackWords.signature inst WNear.Binary.PackWords.function)
  index161:p.mi.funcAddrs[161]?=some p.address161
  function161:s.funcs[p.address161]?=some (.wasm WNear.Binary.StateDecodeBorshRead.signature inst WNear.Binary.StateDecodeBorshRead.function)
  index951:p.mi.funcAddrs[951]?=some p.address951
  function951:s.funcs[p.address951]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature inst WNear.Binary.UnwrapState.Copy.function)
  index68:p.mi.funcAddrs[68]?=some p.address68
  function68:s.funcs[p.address68]?=some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function68)
  index237:p.mi.funcAddrs[237]?=some p.address237
  function237:s.funcs[p.address237]?=some (.wasm WNear.Binary.Deallocate.entrySignature inst WNear.Binary.Deallocate.entryFunction)
  index582:p.mi.funcAddrs[582]?=some p.address582
  function582:s.funcs[p.address582]?=some (.wasm WNear.Binary.Deallocate.coreSignature inst WNear.Binary.Deallocate.coreFunction)

theorem Code.transport(s t:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236)(hf:t.funcs=s.funcs)(hm:t.modules=s.modules)(ht:t.tables=s.tables):
    Code t inst p extra a581 a236:=by
  have storage:=hc.storage.transport s t inst p.toStorage extra hf hm ht
  have decoder:=hc.decoder.transport s t inst p.decoderTemplate p.allocationTemplate a581 a236 hf hm ht
  have release:=hc.release.transport s t inst p.releaseTemplate hf hm
  refine {hc with storage:=storage,decoder:=decoder,release:=release,vectorModule:=?_,function778:=?_,function747:=?_,function777:=?_,function311:=?_,function548:=?_,function779:=?_,function161:=?_,function951:=?_,function68:=?_,function237:=?_,function582:=?_}
  · rw[hm];exact hc.vectorModule
  · rw[hf];exact hc.function778
  · rw[hf];exact hc.function747
  · rw[hf];exact hc.function777
  · rw[hf];exact hc.function311
  · rw[hf];exact hc.function548
  · rw[hf];exact hc.function779
  · rw[hf];exact hc.function161
  · rw[hf];exact hc.function951
  · rw[hf];exact hc.function68
  · rw[hf];exact hc.function237
  · rw[hf];exact hc.function582
theorem Code.module(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):s.modules[inst]?=some p.mi:=hc.storage.register.prefixCode.module

theorem Code.memoryIndex(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):p.mi.memAddrs[0]?=some p.memoryIndex:=hc.storage.register.prefixCode.memoryIndex

theorem Code.globalIndex(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):p.mi.globalAddrs[0]?=some p.globalIndex:=hc.storage.register.prefixCode.globalIndex

theorem Code.decoder_module(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):p.decoderTemplate.mi=p.mi:=by
  have h:=hc.decoder.child.child.prefixCode.child.module
  rw[hc.module s inst p extra a581 a236] at h
  exact Option.some.inj h.symm

theorem Code.release_module(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):p.releaseTemplate.mi=p.mi:=by
  have h:=hc.release.module
  rw[hc.module s inst p extra a581 a236] at h
  exact Option.some.inj h.symm

theorem Code.vector_module(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):p.vectorTemplate.mi=p.mi:=by
  have h:=hc.vectorModule
  rw[hc.module s inst p extra a581 a236] at h
  exact Option.some.inj h.symm
end WNear.Proofs.StateReadOuter
