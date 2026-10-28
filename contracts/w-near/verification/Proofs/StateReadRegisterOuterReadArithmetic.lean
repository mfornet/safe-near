import Proofs.StateReadRegisterOuterReadMemory
import Proofs.PanicAllocateReadback
import NearVM.MemoryListRules

/-! The435 release address is the copied counter word only after proving alignment.
A fresh payload copy leaves that exact word intact before the actual cleanup. -/
namespace WNear.Proofs.StateReadRegisterOuterReadMemory
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32

theorem or4_aligned (scratch : UInt32) (ha : scratch.toNat%16=0)
    (hb : scratch.toNat+16≤2^32) : ((scratch+8)|||4).toNat=scratch.toNat+12 := by
  have next : (scratch+8).toNat=scratch.toNat+8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  rw [UInt32.toNat_or,next]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  have rem : (scratch.toNat+8)%16=8 := by omega
  have div := Nat.or_div_two_pow (a:=scratch.toNat+8) (b:=4) (n:=4)
  have mod := Nat.or_mod_two_pow (a:=scratch.toNat+8) (b:=4) (n:=4)
  simp only [Nat.reducePow,Nat.reduceDiv,Nat.or_zero] at div
  simp only [Nat.reducePow,rem,Nat.reduceMod] at mod
  have numeric : (8 : Nat)|||4=12 := rfl
  rw [numeric] at mod
  have a := Nat.mod_add_div ((scratch.toNat+8)|||4) 16
  have b := Nat.mod_add_div (scratch.toNat+8) 16
  omega

theorem low_counter_word (p : StateDispatchRead.Layout) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize) :
    readI32 (StateDispatchRead.lowMemory p) ((StateDispatchRead.scratch p).toNat+12)=1074904 := by
  let scratch := StateDispatchRead.scratch p
  let memory := StateDispatchRead.acquiredMemory p
  let high := StateDispatchRead.highMemory p
  have a := acquired_spec p hw hc (by omega)
  have highEq : high=writeI32 memory (scratch.toNat+12) 1074904 := by
    change writeI32 memory (scratch.toNat+12) (readI32 memory (scratch.toNat+4))=_
    rw [a.2.2.2.2]
  have h := writeI32_spec memory (scratch.toNat+12) 1074904 a.1 (by rw [a.2.1];exact hb)
  have highWf : high.wf := by rw [highEq];exact h.1
  have highSize : high.byteSize=p.memory.byteSize := by rw [highEq,h.2.1,a.2.1]
  have lowEq : StateDispatchRead.lowMemory p=writeI32 high (scratch.toNat+8) (StateDispatchRead.borrowed p) := rfl
  rw [lowEq]
  have frame := PanicAllocateReadback.read_write_frame high (scratch.toNat+12) (scratch.toNat+8)
    (StateDispatchRead.borrowed p) highWf (by rw [highSize];dsimp only [scratch];omega) (Or.inr (by omega))
  rw [frame,highEq]
  exact PanicAllocateReadback.read_write_self memory (scratch.toNat+12) 1074904 a.1 (by rw [a.2.1];exact hb)

theorem counter_after_payload (p : StateDispatchRead.Layout) (bytes : List UInt8) (hw : p.memory.wf)
    (hc : 1074908≤p.memory.byteSize) (hb : (StateDispatchRead.scratch p).toNat+16≤p.memory.byteSize)
    (ha : (StateDispatchRead.scratch p).toNat%16=0)
    (hwidth : (StateDispatchRead.scratch p).toNat+16≤2^32)
    (hp : (StateDispatchRead.scratch p).toNat+16≤(StateDispatchRead.ptr p).toNat)
    (hpayload : (StateDispatchRead.ptr p).toNat+bytes.length≤p.memory.byteSize) :
    StateDispatchRead.counter p bytes=1074904 := by
  have shape := low_spec p hw hc hb
  have address := or4_aligned (StateDispatchRead.scratch p) ha hwidth
  unfold StateDispatchRead.counter StateDispatchRead.readMemory
  rw [address]
  have span : (StateDispatchRead.ptr p).toNat+bytes.length≤(StateDispatchRead.lowMemory p).byteSize := by
    rw [shape.2.1];exact hpayload
  rw [readI32_writeList_away (StateDispatchRead.lowMemory p) (StateDispatchRead.ptr p).toNat
    ((StateDispatchRead.scratch p).toNat+12) bytes shape.1 span (Or.inl (by omega))]
  exact low_counter_word p hw hc hb
end WNear.Proofs.StateReadRegisterOuterReadMemory
