import Proofs.StateReadResultCall
import Proofs.StorePairReadback
import Proofs.ValueReturnOuterLayout

/-! Exact memory and functional frames for accepted f498. -/
namespace WNear.Proofs.StateReadResult
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
attribute [local irreducible] readI32 readI64 writeI32 writeI64

 theorem finalMemory_spec (memory : Memory) (out source : UInt32) (hwf : memory.wf)
    (hlo : out.toNat + 8 ≤ memory.byteSize) (hhi : (out + 8).toNat + 4 ≤ memory.byteSize) :
    (finalMemory memory out source).wf ∧
    (finalMemory memory out source).byteSize = memory.byteSize ∧
    (finalMemory memory out source).max = memory.max ∧
    ∀ j, (finalMemory memory out source).read8 j =
      if (out + 8).toNat ≤ j ∧ j < (out + 8).toNat + 4 then
        UInt8.ofNat ((readI32 (lowMemory memory out source) (source + 8).toNat).toNat >>> (8 * (j - (out + 8).toNat)))
      else if out.toNat ≤ j ∧ j < out.toNat + 8 then
        UInt8.ofNat ((readI64 memory source.toNat).toNat >>> (8 * (j - out.toNat)))
      else memory.read8 j := by
  have lo := writeI64_spec memory out.toNat (readI64 memory source.toNat) hwf hlo
  have hi := writeI32_spec (lowMemory memory out source) (out + 8).toNat
    (readI32 (lowMemory memory out source) (source + 8).toNat) lo.1 (by rw [show (lowMemory memory out source).byteSize = memory.byteSize from lo.2.1]; exact hhi)
  refine ⟨hi.1,hi.2.1.trans lo.2.1,hi.2.2.1.trans lo.2.2.1,?_⟩
  intro j
  unfold finalMemory
  rw [hi.2.2.2 j]
  rw [show (lowMemory memory out source).read8 j = _ from lo.2.2.2 j]

 theorem finalMemory_read_high (memory : Memory) (out source : UInt32) (hwf : memory.wf)
    (hlo : out.toNat + 8 ≤ memory.byteSize) (hhi : (out + 8).toNat + 4 ≤ memory.byteSize) :
    readI32 (finalMemory memory out source) (out + 8).toNat = readI32 (lowMemory memory out source) (source + 8).toNat := by
  have spec := finalMemory_spec memory out source hwf hlo hhi
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  rw [spec.2.2.2 ((out + 8).toNat + i)]
  simp only [show (out + 8).toNat ≤ (out + 8).toNat + i ∧ (out + 8).toNat + i < (out + 8).toNat + 4 by omega,and_self,ite_true,Nat.add_sub_cancel_left]

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

 theorem highStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]? = some memory) :
    (highStore s op index memory out source).mems[index]? = some (writeI32 memory (out + 8).toNat (readI32 memory (source + 8).toNat)) := by
  have hp : (paid s op 8).mems[index]? = some memory := by rw [paid_mems]; exact hm
  exact storeI32_memory (paid s op 8) index (out + 8).toNat memory (readI32 memory (source + 8).toNat) hp

 theorem after_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]? = some memory) :
    (after s op index memory out source).mems[index]? = some (finalMemory memory out source) := by
  have h0 : (paid (paid s op 3) op 4).mems[index]? = some memory := by rw [paid_mems,paid_mems]; exact hm
  have h1 : (lowStore (paid s op 3) op index memory out source).mems[index]? = some (lowMemory memory out source) :=
    storeI64_memory (paid (paid s op 3) op 4) index out.toNat memory (readI64 memory source.toNat) h0
  exact highStore_memory (lowStore (paid s op 3) op index memory out source) op index (lowMemory memory out source) out source h1

 theorem after_fields (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    (after s op index memory out source).funcs = s.funcs ∧
    (after s op index memory out source).modules = s.modules ∧
    (after s op index memory out source).tables = s.tables ∧
    (after s op index memory out source).globals = s.globals := by
  simp only [after,highStore,lowStore,storeI32_funcs,storeI64_funcs,storeI32_modules,storeI64_modules,
    storeI32_tables,storeI64_tables,storeI32_globals,storeI64_globals,paid,chargedStore]
  exact ⟨trivial,trivial,trivial,trivial⟩

 theorem after_host (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    {(after s op index memory out source).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  simp only [after,highStore,lowStore,storeI32,storeI64,paid,chargedStore,chargeHost]

 theorem after_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (15 * op + rest)) :
    (after s op index memory out source).host.gas.burnt = s.host.gas.burnt + 15 * op ∧
    (after s op index memory out source).host.gas.promises = s.host.gas.promises ∧
    (after s op index memory out source).host.gas.Credits rest := by
  have hg := paid_gas s op 3 (12 * op + rest) (hc.mono (by omega))
  have cg := paid_credits s op 3 (12 * op + rest) (hc.mono (by omega))
  have hl := paid_gas (paid s op 3) op 4 (8 * op + rest) (cg.mono (by omega))
  have cl := lowStore_credits (paid s op 3) op index (8 * op + rest) memory out source (cg.mono (by omega))
  have hh := paid_gas (lowStore (paid s op 3) op index memory out source) op 8 rest cl
  refine ⟨?_,hh.2.trans (hl.2.trans hg.2),after_credits s op index rest memory out source hc⟩
  change (paid (lowStore (paid s op 3) op index memory out source) op 8).host.gas.burnt = _
  rw [hh.1]
  change (paid (paid s op 3) op 4).host.gas.burnt + 8 * op = _
  rw [hl.1,hg.1]; omega

 theorem callAfter_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]? = some memory) :
    (callAfter s op index memory out source).mems[index]? = some (finalMemory memory out source) :=
  after_memory (entered s op) op index memory out source hm

 theorem callAfter_fields (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    (callAfter s op index memory out source).funcs = s.funcs ∧
    (callAfter s op index memory out source).modules = s.modules ∧
    (callAfter s op index memory out source).tables = s.tables ∧
    (callAfter s op index memory out source).globals = s.globals :=
  after_fields (entered s op) op index memory out source

 theorem callAfter_host (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    {(callAfter s op index memory out source).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := by
  have h := after_host (entered s op) op index memory out source
  have h' := congrArg (fun host : NearState => {host with gas := s.host.gas,gasProfile := s.host.gasProfile}) h
  simpa only [callAfter,entered,chargedStore,chargeHost] using h'

 theorem callAfter_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (27 * op + rest)) :
    (callAfter s op index memory out source).host.gas.burnt = s.host.gas.burnt + 27 * op ∧
    (callAfter s op index memory out source).host.gas.promises = s.host.gas.promises ∧
    (callAfter s op index memory out source).host.gas.Credits rest := by
  have h0 := GasCounter.burn_credits s.host.gas op (11 * op + (15 * op + rest)) (hc.mono (by omega))
  have h1 := GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (15 * op + rest) h0.2.2.2
  have h2 := after_gas (entered s op) op index rest memory out source h1.2.2.2
  refine ⟨?_,h2.2.1.trans (h1.2.2.1.trans h0.2.2.1),h2.2.2⟩
  rw [callAfter,h2.1]
  change (chargedStore (chargedStore s op) (11 * op)).host.gas.burnt + 15 * op = _
  have b0 : (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op := h0.2.1
  have b1 : (chargedStore (chargedStore s op) (11 * op)).host.gas.burnt = (chargedStore s op).host.gas.burnt + 11 * op := h1.2.1
  rw [b1,b0]; omega

end WNear.Proofs.StateReadResult
