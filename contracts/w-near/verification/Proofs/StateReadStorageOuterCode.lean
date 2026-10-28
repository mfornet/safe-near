import Proofs.StateReadStorageOuterBorrow
import Proofs.StateReadRegisterOuterCode
import Proofs.StateReadResult

/-! All548 selector and code facts refer to original arrays and original memory. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
attribute [local irreducible] readI32

structure Code (s : Store NearState) (inst : Nat) (p : Layout) (extra : Nat) : Prop where
  register : StateReadRegisterOuter.Code s inst p.toRegisterOuter extra
  storageElement : p.table.elems[(readI32 p.memory (p.dispatchVtable.toNat+188)).toNat]?=some (.func 284)
  storageType : p.mi.types[6]?=some WNear.Binary.StateRead.storageForwardSignature
  storageIndex : p.mi.funcAddrs[284]?=some 284
  storageFunction : s.funcs[284]?=some (.wasm WNear.Binary.StateRead.storageForwardSignature inst WNear.Binary.StateRead.storageForwardFunction)
  hostIndex : p.mi.funcAddrs[43]?=some 43
  hostFunction : s.funcs[43]?=some (.host (metered extra "storage_read" storageReadFn).toHostFn)
  index459 : p.mi.funcAddrs[459]?=some p.address459
  function459 : s.funcs[p.address459]?=some (.wasm WNear.Binary.StateDispatchStorage.signature inst WNear.Binary.StateDispatchStorage.function)
  index523 : p.mi.funcAddrs[523]?=some p.address523
  function523 : s.funcs[p.address523]?=some (.wasm WNear.Binary.StateReadRegisterOuter.signature inst WNear.Binary.StateReadRegisterOuter.function)
  index498 : p.mi.funcAddrs[498]?=some p.address498
  function498 : s.funcs[p.address498]?=some (.wasm WNear.Binary.StateRead.resultSignature inst WNear.Binary.StateRead.resultFunction)

theorem storage_vtable_eq (p : Layout) (hn : Native p) : StateDispatchStorage.vtable (storageLayout p)=p.dispatchVtable := by
  unfold StateDispatchStorage.vtable StateDispatchLength.vtable
  rw [selected_eq p hn]
  change readI32 (StateDispatchLength.lowMemory (storageLayout p)) 1074912=p.dispatchVtable
  exact (low_static_word p hn 1074912 (by have := hn.staticAbove;omega) (Or.inr (by decide))).trans hn.register.vtableRead

theorem storage_element_eq (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    StateDispatchStorage.element (storageLayout p)=readI32 p.memory (p.dispatchVtable.toNat+188) := by
  unfold StateDispatchStorage.element
  rw [storage_vtable_eq p hn]
  have above : p.sp548.toNat≤p.dispatchVtable.toNat+188 := by have := hn.vtableAbove;omega
  have sep : p.dispatchVtable.toNat+188+4≤1074904 := by
    have h:=hn.vtableBeforeHeap
    rw [ha] at h
    change p.dispatchVtable.toNat+192≤1074896 at h
    omega
  exact low_static_word p hn _ above (Or.inl sep)

theorem Code.storageCode (s : Store NearState) (inst : Nat) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (h : Code s inst p extra) :
    StateDispatchStorage.Code s (storageLayout p) inst extra := by
  have pc : StateDispatchPrefix.Code s (storageLayout p).toLayout inst := {h.register.prefixCode with}
  refine ⟨pc,h.register.nonnullIndex,h.register.nonnullFunction,h.register.releaseIndex,h.register.releaseFunction,
    h.register.swapIndex,h.register.swapFunction,h.register.returnIndex,h.register.returnFunction,?_,
    h.storageType,h.storageIndex,h.storageFunction,h.hostIndex,h.hostFunction⟩
  rw [storage_element_eq p hn ha]
  exact h.storageElement

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (extra : Nat)
    (h : Code s inst p extra) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    Code t inst p extra := by
  refine ⟨h.register.transport s t inst p.toRegisterOuter extra hf hm ht,
    h.storageElement,h.storageType,h.storageIndex,?_,h.hostIndex,?_,h.index459,?_,h.index523,?_,h.index498,?_⟩ <;> rw [hf]
  · exact h.storageFunction
  · exact h.hostFunction
  · exact h.function459
  · exact h.function523
  · exact h.function498
end WNear.Proofs.StateReadStorageOuter
