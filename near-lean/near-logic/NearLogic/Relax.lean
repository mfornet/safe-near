import NearLogic.Outcome
import Wasm.HostInvariant
import NearLogic.Charges
import NearVM.GasInvariants

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

/-! ## Charges under raised limits -/

section Charges

open Wasm.Near

/-- The host with its gas limits raised to `p` (prepaid) and `m` (burn limit). -/
def relax (h : NearState) (p m : Nat) : NearState :=
  { h with gas := { h.gas with prepaid := p, maxBurnt := m } }

theorem deduct_relax (g : Near.GasCounter) (burn use p m : Nat) (hp : g.prepaid ≤ p) (hm : g.maxBurnt ≤ m)
    (h : (g.deduct burn use).2 = none) :
    ({ g with prepaid := p, maxBurnt := m } : Near.GasCounter).deduct burn use =
      ({ (g.deduct burn use).1 with prepaid := p, maxBurnt := m }, none) := by
  unfold Near.GasCounter.deduct at h ⊢
  by_cases hc : g.burnt + burn ≤ g.maxBurnt ∧ g.burnt + burn + (g.promises + (use - burn)) ≤ g.prepaid
  · have hc' : g.burnt + burn ≤ m ∧ g.burnt + burn + (g.promises + (use - burn)) ≤ p := by omega
    simp only [hc', and_self, ite_true, hc]
  · simp only [hc, ite_false] at h
    cases h

theorem applyCharge_relax (ns : NearState) (c : Charge) (p m : Nat) (hp : ns.gas.prepaid ≤ p)
    (hm : ns.gas.maxBurnt ≤ m) (h : (applyCharge ns c).2 = none) :
    applyCharge (relax ns p m) c = (relax (applyCharge ns c).1 p m, none) := by
  cases c <;> simp only [applyCharge, relax, Near.GasCounter.burn, Near.GasCounter.prepay,
    Near.GasCounter.payAction] at h ⊢ <;>
    rw [deduct_relax _ _ _ p m hp hm h] <;> rfl

theorem applyCharge_limits (ns : NearState) (c : Charge) :
    (applyCharge ns c).1.gas.prepaid = ns.gas.prepaid ∧ (applyCharge ns c).1.gas.maxBurnt = ns.gas.maxBurnt :=
  applyCharge_gas_limits ns c

/-- Charges that succeed under the lower limits succeed under the raised ones,
with the same result. -/
theorem applyCharges_relax (ns : NearState) (cs : List Charge) (p m : Nat) (hp : ns.gas.prepaid ≤ p)
    (hm : ns.gas.maxBurnt ≤ m) (h : (applyCharges ns cs).2 = none) :
    applyCharges (relax ns p m) cs = (relax (applyCharges ns cs).1 p m, none) := by
  induction cs generalizing ns with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨hl1, hl2⟩ := applyCharge_limits ns c
    cases hc : applyCharge ns c with
    | mk ns' e =>
      cases e with
      | some e => simp [applyCharges, hc] at h
      | none =>
        have hc2 : (applyCharge ns c).2 = none := by rw [hc]
        simp only [applyCharges, hc] at h ⊢
        rw [applyCharge_relax ns c p m hp hm hc2, hc]
        simp only
        rw [hc] at hl1 hl2
        exact ih ns' (by rw [hl1]; exact hp) (by rw [hl2]; exact hm) h

end Charges

end NearLogic
