import Mathlib.Tactic.IntervalCases
import Model.Storage
import Proofs.TotalSupply
import Proofs.StorePairReadback
import WasmEmbed.Embed

/-! Model header bytes determine actual little-endian guest memory reads.
No successful guest decode or contract execution is a premise. -/
namespace WNear.Proofs.StateReadHeaderBytes
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

 theorem accountsPrefix_bytes : WNear.accountsPrefix=[97] := by kernel_rfl

theorem header_layout (state : WNear.State) :
    WNear.header state=[1,0,0,0,97]++Borsh.leBytes 16 state.totalSupply++Borsh.leBytes 8 state.accountStorageUsage := by
  unfold WNear.header
  rw [accountsPrefix_bytes]
  rfl

theorem header_length (state : WNear.State) : (WNear.header state).length=29 := by
  rw [header_layout]
  simp only [List.length_append,Borsh.leBytes_length,List.length_cons,List.length_nil]

theorem leBytes_byte (width value i : Nat) (hi : i<width) :
    (Borsh.leBytes width value)[i]! =UInt8.ofNat (value/256^i) := by
  induction width generalizing value i with
  | zero => omega
  | succ width ih =>
    cases i with
    | zero =>
      simp only [NearSdk.Borsh.leBytes,List.getElem!_cons_zero,Nat.pow_zero,Nat.div_one]
      apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_ofNat',Nat.reducePow,Nat.mod_mod]
    | succ i =>
      simp only [NearSdk.Borsh.leBytes,List.getElem!_cons_succ]
      rw [ih (value/256) i (by omega),Nat.div_div_eq_div_mul]
      congr 2
      rw [Nat.pow_succ,Nat.mul_comm]

private theorem get_append_left (a b : List UInt8) (i : Nat) (hi : i<a.length) :
    (a++b)[i]! =a[i]! := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_append_left hi]
private theorem get_append_right (a b : List UInt8) (i : Nat) :
    (a++b)[a.length+i]! =b[i]! := by
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]

theorem header_supply_byte (state : WNear.State) (i : Nat) (hi : i<16) :
    (WNear.header state)[5+i]! =UInt8.ofNat (state.totalSupply/256^i) := by
  rw [header_layout,List.append_assoc]
  have first := get_append_right [1,0,0,0,97] (Borsh.leBytes 16 state.totalSupply++Borsh.leBytes 8 state.accountStorageUsage) i
  change _[5+i]! =_ at first
  rw [first,get_append_left _ _ i (by simp only [Borsh.leBytes_length];exact hi)]
  exact leBytes_byte 16 state.totalSupply i hi

theorem header_usage_byte (state : WNear.State) (i : Nat) (hi : i<8) :
    (WNear.header state)[21+i]! =UInt8.ofNat (state.accountStorageUsage/256^i) := by
  rw [header_layout]
  have first := get_append_right ([1,0,0,0,97]++Borsh.leBytes 16 state.totalSupply) (Borsh.leBytes 8 state.accountStorageUsage) i
  simp only [List.length_append,Borsh.leBytes_length,List.length_cons,List.length_nil,Nat.reduceAdd] at first
  rw [first]
  exact leBytes_byte 8 state.accountStorageUsage i hi

theorem read_word_bytes (memory : Memory) (address value : Nat)
    (h : ∀ i, i<8 → memory.read8 (address+i)=UInt8.ofNat (value/256^i)) :
    readI64 memory address=UInt64.ofNat value := by
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  rw [h i hi]
  apply UInt8.toNat_inj.mp
  interval_cases i <;> simp only [UInt64.toNat_ofNat',UInt8.toNat_ofNat',Nat.shiftRight_eq_div_pow,Nat.reduceMul,Nat.reducePow,Nat.div_one] <;> omega

/-- The exact header occupies29 bytes at the payload address. -/
def At (memory : Memory) (payload : Nat) (state : WNear.State) : Prop :=
  ∀ i, i<29 → memory.read8 (payload+i)=(WNear.header state)[i]!

theorem read_header (memory : Memory) (payload : Nat) (state : WNear.State) (hw : state.WF)
    (h : At memory payload state) :
    readI32 memory payload=1 ∧ memory.read8 (payload+4)=97 ∧
    TotalSupply.U128At memory (payload+5) state.totalSupply ∧
    readI64 memory (payload+21)=UInt64.ofNat state.accountStorageUsage := by
  have leading (i : Nat) (hi : i<4) : memory.read8 (payload+i)=if i=0 then 1 else 0 := by
    rw [h i (by omega),header_layout]
    interval_cases i <;> rfl
  have byte0 : memory.read8 payload=1 := by simpa only [Nat.add_zero,ite_true] using leading 0 (by decide)
  have first : readI32 memory payload=1 := by
    simp [readI32,List.range_succ,leading,byte0]
  have tag : memory.read8 (payload+4)=97 := by
    rw [h 4 (by decide),header_layout]
    rfl
  have low : readI64 memory (payload+5)=UInt64.ofNat state.totalSupply := by
    apply read_word_bytes
    intro i hi
    rw [Nat.add_assoc,h (5+i) (by omega),header_supply_byte state i (by omega)]
  have high : readI64 memory (payload+13)=UInt64.ofNat (state.totalSupply/2^64) := by
    apply read_word_bytes
    intro i hi
    have address : payload+13+i=payload+(5+(8+i)) := by omega
    rw [address,h (5+(8+i)) (by omega),header_supply_byte state (8+i) (by omega)]
    have factor : 256^(8+i)=2^64*256^i := by rw [Nat.pow_add];rfl
    rw [factor,Nat.div_div_eq_div_mul]
  have usage : readI64 memory (payload+21)=UInt64.ofNat state.accountStorageUsage := by
    apply read_word_bytes
    intro i hi
    rw [Nat.add_assoc,h (21+i) (by omega),header_usage_byte state i hi]
  have supply := hw.totalSupply_lt
  change state.totalSupply<2^128 at supply
  have highBound : state.totalSupply/2^64<2^64 := by omega
  have represented : TotalSupply.U128At memory (payload+5) state.totalSupply := by
    unfold TotalSupply.U128At
    have address : payload+5+8=payload+13 := by omega
    rw [address,low,high,UInt64.toNat_ofNat',UInt64.toNat_ofNat',Nat.mod_eq_of_lt highBound]
    omega
  exact ⟨first,tag,represented,usage⟩
end WNear.Proofs.StateReadHeaderBytes
