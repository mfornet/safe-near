import NearVM.MeteredHosts.StorageReadContract

/-! Observable register and memory facts for canonical read results. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open StorageMetered
open _root_.Near.TrieOverlay
set_option maxRecDepth 16384

theorem result_memory (before : HostStore NearState) (keyLen keyPtr register : UInt64)
    (initial : State) (p : ReadPlan) (value : List UInt8) :
    (result before keyLen keyPtr register initial p value).mem = before.mem := by
  unfold result written
  split <;> rfl

/-- Pre-call billing, trie preparation, and post-call billing frame every
register except the one written by the real raw read. -/
theorem result_registers (before : HostStore NearState) (keyLen keyPtr register : UInt64)
    (initial : State) (p : ReadPlan) (value : List UInt8) :
    (result before keyLen keyPtr register initial p value).host.registers =
      if register = u64Max then before.host.registers else
        fun i => if i = register.toNat then some value else before.host.registers i := by
  let b := beforeTrie before keyLen keyPtr register
  let phase := p.result b initial
  let output := written phase register value
  have pre := congrArg NearState.registers (applyCharges_frame before.host (preCharges before keyLen keyPtr register)
    (beforeCharges_burnsOnly before keyLen keyPtr register))
  have post := congrArg NearState.registers (applyCharges_frame output.host (writeReg value.length) (writeReg_burnsOnly value.length))
  change (applyCharges output.host (writeReg value.length)).1.registers = _
  change (applyCharges output.host (writeReg value.length)).1.registers = output.host.registers at post
  rw [post]
  change (prePaid before keyLen keyPtr register).registers = before.host.registers at pre
  unfold output written
  split
  · simp only [phase, ReadPlan.result, prepared, b, beforeTrie, Output.paidStore, pre]
  · simp only [NearState.setRegister, phase, ReadPlan.result, prepared, b, beforeTrie, Output.paidStore, pre]

theorem result_register (before : HostStore NearState) (keyLen keyPtr register : UInt64)
    (initial : State) (p : ReadPlan) (value : List UInt8) (h : register ≠ u64Max) :
    (result before keyLen keyPtr register initial p value).host.registers register.toNat = some value := by
  rw [result_registers]
  simp [h]

end Wasm.Near.MeteredHosts.StorageRead
