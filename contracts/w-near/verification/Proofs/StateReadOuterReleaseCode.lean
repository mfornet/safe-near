import Proofs.StateReadOuterCode
import Proofs.StateReadOuterNative

/-! Original installed descriptors transport to219's sequential release layout.
The resource constructor is an intermediate assembly lemma: the public original
domain must establish its heap and saved-vector bounds. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] outputMemory
  VectorDropPositive.pointer VectorDropPositive.capacity

theorem Code.releaseActual(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):
    DeallocateCore.Code s inst (actualRelease p):=by
  exact ⟨hc.release.module,hc.release.memoryIndex,hc.release.index568,hc.release.function568,
    hc.release.index570,hc.release.function570,hc.release.index575,hc.release.function575,
    hc.release.index576,hc.release.function576⟩

theorem Code.release_memoryIndex(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):p.releaseTemplate.memoryIndex=p.memoryIndex:=by
  have h:=hc.release.memoryIndex
  rw[hc.release_module s inst p extra a581 a236,hc.memoryIndex s inst p extra a581 a236] at h
  exact Option.some.inj h.symm

theorem Code.vector_memoryIndex(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hc:Code s inst p extra a581 a236):p.vectorTemplate.memoryIndex=p.memoryIndex:=by
  have h:=hc.vectorMemoryIndex
  rw[hc.vector_module s inst p extra a581 a236,hc.memoryIndex s inst p extra a581 a236] at h
  exact Option.some.inj h.symm

theorem release_resources_of_heap(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hn:Native p)(hc:Code s inst p extra a581 a236)
    (hm:s.mems[p.memoryIndex]?=some (outputMemory p))
    (heap:DeallocateInsert.Native (actualRelease p))
    (bound:(scratch p+24).toNat+8≤(outputMemory p).byteSize):
    VectorDropInsert.Resources s inst (actualVector p) (actualRelease p)
      p.address68 p.address237 p.address582:=by
  have rmi:=hc.release_memoryIndex s inst p extra a581 a236
  have vmi:=hc.vector_memoryIndex s inst p extra a581 a236
  have vector:VectorDropPositive.Ready s inst (actualVector p):=by
    refine ⟨hc.vectorModule,hc.vectorMemoryIndex,?_,hc.index778,hc.function778,
      hc.index747,hc.function747,hc.index777,hc.function777,hc.index311,hc.function311,bound,?_⟩
    · change s.mems[p.vectorTemplate.memoryIndex]?=some (outputMemory p)
      rw[vmi];exact hm
    · exact heap.lengthNonzero
  have release:VectorDropInsert237.Ready s inst (actualRelease p) p.address582:=by
    refine ⟨hc.releaseActual s inst p extra a581 a236,?_,heap,?_,?_,hc.function582⟩
    · change s.mems[p.releaseTemplate.memoryIndex]?=some (outputMemory p)
      rw[rmi];exact hm
    · change p.releaseTemplate.allocator=1074896
      rw[hn.releaseRoot,hn.allocator]
    · change p.releaseTemplate.mi.funcAddrs[582]?=some p.address582
      rw[hc.release_module s inst p extra a581 a236];exact hc.index582
  refine ⟨vector,release,rfl,rfl,rfl,?_,hc.function237,?_,hc.function68⟩
  · change p.vectorTemplate.mi.funcAddrs[237]?=some p.address237
    rw[hc.vector_module s inst p extra a581 a236];exact hc.index237
  · change p.vectorTemplate.mi.funcAddrs[68]?=some p.address68
    rw[hc.vector_module s inst p extra a581 a236];exact hc.index68
end WNear.Proofs.StateReadOuter
