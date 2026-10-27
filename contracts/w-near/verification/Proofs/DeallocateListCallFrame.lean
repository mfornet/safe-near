import Proofs.DeallocateListCall

/-! Actual local-call gas and structural frames for f575. -/
namespace WNear.Proofs.DeallocateListCall
open Wasm Wasm.Near MeteredLogic
open DeallocateListState
attribute [local irreducible] readI32 writeI32

theorem called_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (called s op p).mems[p.memoryIndex]? = some (finalMemory p) := by
  apply after_memory
  simpa only [entered, chargedStore] using hm

theorem called_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (called s op p).funcs = s.funcs ∧ (called s op p).modules = s.modules ∧
    (called s op p).tables = s.tables ∧ (called s op p).globals = s.globals := by
  simpa only [called, entered, chargedStore] using after_fields (entered s op) op p

theorem called_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(called s op p).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  have h := after_host (entered s op) op p
  have lifted := congrArg (fun h : NearState => {h with gas := s.host.gas, gasProfile := s.host.gasProfile}) h
  simpa only [called, entered, chargedStore, chargeHost] using lifted

theorem called_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (72 * op + rest)) :
    (called s op p).host.gas.burnt = s.host.gas.burnt + 72 * op ∧
    (called s op p).host.gas.promises = s.host.gas.promises ∧
    (called s op p).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (71 * op + rest) (hc.mono (by omega))
  have act := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (61 * op + rest) (hop.2.2.2.mono (by omega))
  have body := after_gas (entered s op) op rest p act.2.2.2
  refine ⟨?_, body.2.1.trans (act.2.2.1.trans hop.2.2.1), body.2.2⟩
  change (after (entered s op) op p).host.gas.burnt = _
  rw [body.1]
  change (chargedStore (chargedStore s op) (10 * op)).host.gas.burnt + 61 * op = _
  change ((chargedStore s op).host.gas.burn (10 * op)).1.burnt + 61 * op = _
  rw [act.2.1]
  change (s.host.gas.burn op).1.burnt + 10 * op + 61 * op = _
  rw [hop.2.1]; omega

end WNear.Proofs.DeallocateListCall
