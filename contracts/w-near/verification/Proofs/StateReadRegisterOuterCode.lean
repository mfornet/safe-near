import Proofs.StateReadRegisterOuterLengthNative
import Proofs.StateReadRegisterOuterReadState
import Proofs.StateDispatchReadState

/-! All523 code assumptions concern original arrays and original static selector
words. No code lookup at a future callee store is an input. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
attribute [local irreducible] readI32 StateDispatchLength.element

structure Code (s : Store NearState) (inst : Nat) (p : Layout) (extra : Nat) : Prop where
  vector : AllocateVectorOuter.Code s inst p.toVectorOuter
  prefixCode : StateDispatchPrefix.Code s (actualLength p).inner.toLayout inst
  nonnullIndex : p.mi.funcAddrs[430]?=some 430
  nonnullFunction : s.funcs[430]?=some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction)
  releaseIndex : p.mi.funcAddrs[431]?=some 431
  releaseFunction : s.funcs[431]?=some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction)
  swapIndex : p.mi.funcAddrs[672]?=some 672
  swapFunction : s.funcs[672]?=some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  returnIndex : p.mi.funcAddrs[432]?=some 432
  returnFunction : s.funcs[432]?=some (.wasm WNear.Binary.StateDispatch.returnSignature inst WNear.Binary.StateDispatch.returnFunction)
  lengthElement : p.table.elems[(readI32 p.memory (p.dispatchVtable.toNat+16)).toNat]?=some (.func 241)
  lengthType : p.mi.types[7]?=some WNear.Binary.StateRead.lengthForwardSignature
  lengthIndex : p.mi.funcAddrs[241]?=some 241
  lengthFunction : s.funcs[241]?=some (.wasm WNear.Binary.StateRead.lengthForwardSignature inst WNear.Binary.StateRead.lengthForwardFunction)
  hostIndex : p.mi.funcAddrs[1]?=some 1
  hostFunction : s.funcs[1]?=some (.host (metered extra "register_len" registerLenFn).toHostFn)
  innerLengthIndex : p.mi.funcAddrs[440]?=some 440
  innerLengthFunction : s.funcs[440]?=some (.wasm WNear.Binary.StateDispatchLength.signature inst WNear.Binary.StateDispatchLength.function)
  index524 : p.mi.funcAddrs[524]?=some p.address524
  function524 : s.funcs[p.address524]?=some (.wasm WNear.Binary.StateDispatchLengthOuter.signature inst WNear.Binary.StateDispatchLengthOuter.function)
  index687 : p.mi.funcAddrs[687]?=some p.address687
  function687 : s.funcs[p.address687]?=some (.wasm WNear.Binary.AllocateVectorOuter.signature inst WNear.Binary.AllocateVectorOuter.function)
  index435 : p.mi.funcAddrs[435]?=some p.address435
  function435 : s.funcs[p.address435]?=some (.wasm WNear.Binary.StateDispatchRead.signature inst WNear.Binary.StateDispatchRead.function)
  readCode : StateDispatchRead.Code s (originalReadLayout p) inst extra

theorem length_element_eq (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    StateDispatchLength.element (actualLength p).inner=readI32 p.memory (p.dispatchVtable.toNat+16) := by
  unfold StateDispatchLength.element
  rw [length_vtable_eq p hn]
  have above : p.sp523.toNat≤p.dispatchVtable.toNat+16 := by have := hn.vtableAbove;omega
  have sep : p.dispatchVtable.toNat+16+4≤1074904 := by
    have before := hn.vtableBeforeHeap
    rw [ha] at before
    change p.dispatchVtable.toNat+20≤1074896 at before
    omega
  exact low_static_word p hn _ above (Or.inl sep)

theorem Code.lengthCode (s : Store NearState) (inst : Nat) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (h : Code s inst p extra) :
    StateDispatchLength.Code s (actualLength p).inner inst extra := by
  refine ⟨h.prefixCode,h.nonnullIndex,h.nonnullFunction,h.releaseIndex,h.releaseFunction,
    h.swapIndex,h.swapFunction,h.returnIndex,h.returnFunction,?_,h.lengthType,h.lengthIndex,h.lengthFunction,h.hostIndex,h.hostFunction⟩
  rw [length_element_eq p hn ha]
  exact h.lengthElement

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (extra : Nat)
    (h : Code s inst p extra) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    Code t inst p extra := by
  refine {h with vector:=h.vector.transport s t inst p.toVectorOuter hf hm ht,
                 prefixCode:=h.prefixCode.transport s t (actualLength p).inner.toLayout inst hf hm ht,
                 nonnullFunction:=?_,releaseFunction:=?_,swapFunction:=?_,returnFunction:=?_,lengthFunction:=?_,hostFunction:=?_,
                 innerLengthFunction:=?_,function524:=?_,function687:=?_,function435:=?_,
                 readCode:=h.readCode.transport s t (originalReadLayout p) inst extra hf hm ht} <;> rw [hf]
  · exact h.nonnullFunction
  · exact h.releaseFunction
  · exact h.swapFunction
  · exact h.returnFunction
  · exact h.lengthFunction
  · exact h.hostFunction
  · exact h.innerLengthFunction
  · exact h.function524
  · exact h.function687
  · exact h.function435
end WNear.Proofs.StateReadRegisterOuter
