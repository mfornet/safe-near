import Proofs.StateReadRegisterOuterReadArithmetic
import Proofs.StateDispatchLengthMemory

/-! Simple initial-snapshot sufficient conditions for435. Every low-memory selector,
register/pointer read and post-payload counter obligation is derived from its writes. -/
namespace WNear.Proofs.StateReadRegisterOuterReadMemory
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32

structure Snapshot (p : StateDispatchRead.Layout) (bytes : List UInt8) (register : UInt64) (pointer vtable : UInt32) : Prop where
  wf : p.memory.wf
  spLower : 16≤p.sp.toNat
  spBound : p.sp.toNat≤p.memory.byteSize
  aligned : p.sp.toNat%16=0
  staticAbove : p.sp.toNat≤1055020
  interface : p.interface=1055020
  interfaceBound : 1055024≤p.memory.byteSize
  interfaceRead : readI32 p.memory 1055020=p.lookupElement
  stateBound : 1074916≤p.memory.byteSize
  threadStatus : readI32 p.memory 1074900=1
  counterZero : readI32 p.memory 1074904=0
  receiverNonzero : readI32 p.memory 1074908≠0
  vtableRead : readI32 p.memory 1074912=vtable
  vtableBound : vtable.toNat+16≤p.memory.byteSize
  vtableAbove : p.sp.toNat≤vtable.toNat
  vtableBeforeCell : vtable.toNat+16≤1074904
  registerAbove : p.sp.toNat≤p.inputRegister.toNat
  registerEnd : p.inputRegister.toNat+8≤1055020
  registerRead : readI64 p.memory p.inputRegister.toNat=register
  pointerAbove : p.sp.toNat≤p.inputPointer.toNat
  pointerEnd : p.inputPointer.toNat+4≤1055020
  pointerRead : readI32 p.memory p.inputPointer.toNat=pointer
  payloadAbove : p.sp.toNat≤pointer.toNat
  payloadBound : pointer.toNat+bytes.length≤p.memory.byteSize

theorem packed32_readI32 (memory : Memory) (address : Nat) :
    ValueReturnDispatch.packed32 memory address=UInt64.ofNat (readI32 memory address).toNat := by
  have h0 := (memory.read8 address).toNat_lt
  have h1 := (memory.read8 (address+1)).toNat_lt
  have h2 := (memory.read8 (address+2)).toNat_lt
  have h3 := (memory.read8 (address+3)).toNat_lt
  have hn : ((List.range 4).foldr (fun i acc => acc*256+(memory.read8 (address+i)).toNat) 0)<2^32 := by
    simp only [List.range_succ,List.foldr_append,List.foldr_cons,List.foldr_nil,List.range_zero,Nat.zero_add,Nat.add_zero,Nat.zero_mul]
    omega
  unfold ValueReturnDispatch.packed32 readI32
  rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt hn]

theorem Snapshot.scratch_nat {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : (StateDispatchRead.scratch p).toNat=p.sp.toNat-16 := by
  have lo := hn.spLower
  have hi := p.sp.toNat_lt
  change (p.sp-16).toNat=_
  rw [UInt32.toNat_sub]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem Snapshot.scratch_bound {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize := by
  have num := hn.scratch_nat
  have lo := hn.spLower
  have bound := hn.spBound
  omega

theorem Snapshot.low_shape {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) :
    (StateDispatchRead.lowMemory p).wf ∧ (StateDispatchRead.lowMemory p).byteSize=p.memory.byteSize ∧
    (StateDispatchRead.lowMemory p).max=p.memory.max := by
  have h := low_spec p hn.wf (by have := hn.stateBound;omega) hn.scratch_bound
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem Snapshot.borrowed {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : StateDispatchRead.borrowed p=1074908 :=
  borrowed_eq p hn.wf (by have := hn.stateBound;omega) hn.scratch_bound

theorem Snapshot.selected {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : StateDispatchRead.selected p=1074908 := by
  have num := hn.scratch_nat
  have lo := hn.spLower
  have above := hn.staticAbove
  exact selected_eq p hn.wf (by have := hn.stateBound;omega) hn.scratch_bound (Or.inr (by omega)) hn.receiverNonzero

theorem Snapshot.vtable {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : StateDispatchRead.vtable p=vtable := by
  have num := hn.scratch_nat
  have lo := hn.spLower
  have above := hn.staticAbove
  unfold StateDispatchRead.vtable
  rw [hn.selected]
  change readI32 (StateDispatchRead.lowMemory p) 1074912=vtable
  rw [low_read_frame p 1074912 hn.wf (by have := hn.stateBound;omega) hn.scratch_bound
    (Or.inr (by omega)) (Or.inr (by omega))]
  exact hn.vtableRead

theorem Snapshot.element {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : StateDispatchRead.element p=readI32 p.memory (vtable.toNat+12) := by
  have num := hn.scratch_nat
  have lo := hn.spLower
  have above := hn.vtableAbove
  have before := hn.vtableBeforeCell
  unfold StateDispatchRead.element
  rw [hn.vtable]
  exact low_read_frame p (vtable.toNat+12) hn.wf (by have := hn.stateBound;omega) hn.scratch_bound
    (Or.inl (by omega)) (Or.inr (by omega))

theorem Snapshot.register_eq {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : StateDispatchRead.register p=register := by
  have num := hn.scratch_nat
  have lo := hn.spLower
  have above := hn.registerAbove
  have bound := hn.registerEnd
  unfold StateDispatchRead.register
  rw [low_readI64_frame p p.inputRegister.toNat hn.wf (by have := hn.stateBound;omega) hn.scratch_bound
    (Or.inl (by omega)) (Or.inr (by omega))]
  exact hn.registerRead

theorem Snapshot.ptr_eq {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : StateDispatchRead.ptr p=UInt64.ofNat pointer.toNat := by
  have num := hn.scratch_nat
  have lo := hn.spLower
  have above := hn.pointerAbove
  have bound := hn.pointerEnd
  unfold StateDispatchRead.ptr
  rw [low_packed32_frame p p.inputPointer.toNat hn.wf (by have := hn.stateBound;omega) hn.scratch_bound
    (Or.inl (by omega)) (Or.inr (by omega)),packed32_readI32,hn.pointerRead]

theorem Snapshot.ptr_nat {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : (StateDispatchRead.ptr p).toNat=pointer.toNat := by
  rw [hn.ptr_eq,UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_trans pointer.toNat_lt (by decide))

theorem Snapshot.counter {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable) : StateDispatchRead.counter p bytes=1074904 := by
  have num := hn.scratch_nat
  have lo := hn.spLower
  have above := hn.payloadAbove
  have bound := hn.payloadBound
  have width := p.sp.toNat_lt
  have align := hn.aligned
  have aligned : (StateDispatchRead.scratch p).toNat%16=0 := by omega
  apply counter_after_payload p bytes hn.wf (by have := hn.stateBound;omega) hn.scratch_bound aligned
  · omega
  · rw [hn.ptr_nat];omega
  · rw [hn.ptr_nat];exact bound
end WNear.Proofs.StateReadRegisterOuterReadMemory
