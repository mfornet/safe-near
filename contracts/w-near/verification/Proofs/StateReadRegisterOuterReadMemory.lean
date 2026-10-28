import Proofs.StateDispatchReadState
import Proofs.ValueReturnOuterLayout
import NearVM.MemoryListWordRules

/-! The actual435 borrow footprint, on any original snapshot. These lemmas expose
only byte/word frames and deterministic record contents, not execution premises. -/
namespace WNear.Proofs.StateReadRegisterOuterReadMemory
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32

def snapshot (p : StateDispatchRead.Layout) : ValueReturnOuterBody.Layout :=
  {mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,tableAddress:=p.tableAddress,
   global:=p.global,table:=p.table,sp:=p.sp,interface:=p.interface,slice:=0,lookupElement:=p.lookupElement,
   receiver:=0,vtable:=0,returnElement:=0,len:=0,ptr:=0,memory:=p.memory}

private theorem memory_snapshot (p : StateDispatchRead.Layout) : (snapshot p).memory=p.memory := rfl

private theorem scratch_snapshot (p : StateDispatchRead.Layout) :
    ValueReturnOuterBody.scratch (snapshot p)=StateDispatchRead.scratch p := rfl
private theorem acquired_snapshot (p : StateDispatchRead.Layout) :
    ValueReturnOuterBody.acquiredMemory (snapshot p)=StateDispatchRead.acquiredMemory p := rfl
private theorem borrowed_snapshot (p : StateDispatchRead.Layout) :
    ValueReturnOuterBody.borrowed (snapshot p)=StateDispatchRead.borrowed p := rfl
private theorem low_snapshot (p : StateDispatchRead.Layout) :
    ValueReturnOuterBody.lowMemory (snapshot p)=StateDispatchRead.lowMemory p := rfl
private theorem selected_snapshot (p : StateDispatchRead.Layout) :
    ValueReturnOuterBody.selected (snapshot p)=StateDispatchRead.selected p := rfl

theorem acquired_spec (p : StateDispatchRead.Layout) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+8≤p.memory.byteSize) :
    (StateDispatchRead.acquiredMemory p).wf ∧
    (StateDispatchRead.acquiredMemory p).byteSize=p.memory.byteSize ∧
    (StateDispatchRead.acquiredMemory p).max=p.memory.max ∧
    readI32 (StateDispatchRead.acquiredMemory p) (StateDispatchRead.scratch p).toNat=1074908 ∧
    readI32 (StateDispatchRead.acquiredMemory p) ((StateDispatchRead.scratch p).toNat+4)=1074904 := by
  have h := ValueReturnOuterLayout.acquired_spec (snapshot p) hw hc hb
  simpa only [acquired_snapshot,scratch_snapshot,memory_snapshot] using
    And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 (And.intro h.2.2.2.1 h.2.2.2.2.1)))

theorem borrowed_eq (p : StateDispatchRead.Layout) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize) :
    StateDispatchRead.borrowed p=1074908 := by
  simpa only [borrowed_snapshot,scratch_snapshot,memory_snapshot] using ValueReturnOuterLayout.borrowed_eq (snapshot p) hw hc hb

theorem low_spec (p : StateDispatchRead.Layout) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize) :
    (StateDispatchRead.lowMemory p).wf ∧ (StateDispatchRead.lowMemory p).byteSize=p.memory.byteSize ∧
    (StateDispatchRead.lowMemory p).max=p.memory.max ∧
    ∀ j, (j<1074904 ∨ 1074908≤j) →
      (j<(StateDispatchRead.scratch p).toNat ∨ (StateDispatchRead.scratch p).toNat+16≤j) →
      (StateDispatchRead.lowMemory p).read8 j=p.memory.read8 j := by
  simpa only [low_snapshot,scratch_snapshot,memory_snapshot] using ValueReturnOuterLayout.low_spec (snapshot p) hw hc hb

theorem low_read_frame (p : StateDispatchRead.Layout) (address : Nat) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize)
    (hcsep : address+4≤1074904 ∨ 1074908≤address)
    (hssep : address+4≤(StateDispatchRead.scratch p).toNat ∨ (StateDispatchRead.scratch p).toNat+16≤address) :
    readI32 (StateDispatchRead.lowMemory p) address=readI32 p.memory address := by
  simpa only [low_snapshot,scratch_snapshot,memory_snapshot] using
    ValueReturnOuterLayout.low_read_frame (snapshot p) address hw hc hb hcsep hssep

theorem low_readI64_frame (p : StateDispatchRead.Layout) (address : Nat) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize)
    (hcsep : address+8≤1074904 ∨ 1074908≤address)
    (hssep : address+8≤(StateDispatchRead.scratch p).toNat ∨ (StateDispatchRead.scratch p).toNat+16≤address) :
    readI64 (StateDispatchRead.lowMemory p) address=readI64 p.memory address := by
  have h := low_spec p hw hc hb
  apply readI64_congr_bytes
  intro i hi
  exact h.2.2.2 (address+i) (by omega) (by omega)

theorem low_packed32_frame (p : StateDispatchRead.Layout) (address : Nat) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize)
    (hcsep : address+4≤1074904 ∨ 1074908≤address)
    (hssep : address+4≤(StateDispatchRead.scratch p).toNat ∨ (StateDispatchRead.scratch p).toNat+16≤address) :
    ValueReturnDispatch.packed32 (StateDispatchRead.lowMemory p) address=ValueReturnDispatch.packed32 p.memory address := by
  simpa only [low_snapshot,scratch_snapshot,memory_snapshot] using
    ValueReturnOuterLayout.low_packed32_frame (snapshot p) address hw hc hb hcsep hssep

theorem selected_eq (p : StateDispatchRead.Layout) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize)
    (hsep : 1074912≤(StateDispatchRead.scratch p).toNat ∨ (StateDispatchRead.scratch p).toNat+16≤1074908)
    (hn : readI32 p.memory 1074908≠0) : StateDispatchRead.selected p=1074908 := by
  simpa only [selected_snapshot,scratch_snapshot,memory_snapshot] using
    ValueReturnOuterLayout.selected_eq (snapshot p) hw hc hb hsep hn
end WNear.Proofs.StateReadRegisterOuterReadMemory
