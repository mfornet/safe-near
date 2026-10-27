import NearLogic.Outcome
import Wasm.HostInvariant

/-!
# Instructions carry the host along

`Exec.instr` never reads the host state: running an instruction on a store
with another host gives the same effect, with that host. This is the first
step towards relating runs that differ only in their host's gas limits
(the below-the-bound case of `Refines`).
-/

namespace NearLogic

open Wasm Wasm.Exec

variable {H : Type}

/-- An effect with its store's host replaced. -/
def _root_.Wasm.Exec.Effect.withHost (e : Effect H) (h : H) : Effect H := { e with store := { e.store with host := h } }

theorem storeNat_withHost (σ : Store H) (h : H) (inst : ModuleInst) (arg : MemArg) (addr : UInt32)
    (len v : Nat) :
    storeNat { σ with host := h } inst arg addr len v =
      (storeNat σ inst arg addr len v).map fun s => { s with host := h } := by
  unfold storeNat Store.memOf Store.setMemOf
  cases h1 : inst.memAddrs[0]? <;> simp [h1]
  rename_i a
  cases σ.mems[a]? <;> simp
  rename_i m
  cases m.writeNat (addr.toNat + arg.offset) len v <;> simp

theorem branch_withHost (σ : Store H) (h : H) (stack : Array Value) (labels : List Label)
    (locals : Array Value) (l : Nat) :
    branch { σ with host := h } stack labels locals l = (branch σ stack labels locals l).withHost h := by
  unfold branch
  dsimp only
  repeat' split
  all_goals rfl

theorem evalMemOp_withHost (σ : Store H) (h : H) (inst : ModuleInst) (stack : Array Value)
    (labels : List Label) (rest : List Instr) (locals : Array Value) (k : Memory → Option Memory) :
    evalMemOp { σ with host := h } inst stack labels rest locals k =
      (evalMemOp σ inst stack labels rest locals k).withHost h := by
  unfold evalMemOp Store.memOf Store.setMemOf
  dsimp only
  repeat' split
  all_goals simp_all [Effect.withHost, Effect.trap, Effect.continue]

set_option maxHeartbeats 4000000 in
theorem instr_withHost (σ : Store H) (h : H) (inst : ModuleInst) (locals stack : Array Value)
    (labels : List Label) (i : Instr) (rest : List Instr) :
    instr { σ with host := h } inst locals stack labels i rest =
      (instr σ inst locals stack labels i rest).withHost h := by
  unfold instr storeEffect
  cases i <;> simp only [Store.memOf, tableOf, loadNat, storeNat_withHost, branch_withHost,
    evalMemOp_withHost] <;> (repeat' split) <;>
    (try simp_all [Effect.withHost, Effect.trap, Effect.continue, Effect.call, Effect.return, branch_withHost,
      evalMemOp_withHost, Store.memOf, Store.setMemOf, setTable, tableOf, loadNat, storeNat_withHost,
      Option.bind_eq_some_iff])
  all_goals (try (repeat' split)) <;> (try simp_all [Effect.withHost, Option.bind_eq_some_iff])

end NearLogic
