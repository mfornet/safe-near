import Proofs.UnwrapStateCopyState

/-! Exact gas of the actual byte-copy loop, including paid backedges. -/
namespace WNear.Proofs.UnwrapStateCopyGas
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.UnwrapStateCopy
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)

/-- The byte write frames gas, so each of the four scalar groups burns four
ordinary units while preserving promise reservations. -/
theorem prefixStore_gas (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (rest : Nat) (hc : s.host.gas.Credits (16 * op + rest)) :
    (prefixStore s op index out source memory).host.gas.burnt = s.host.gas.burnt + 16 * op ∧
    (prefixStore s op index out source memory).host.gas.promises = s.host.gas.promises := by
  let b := byteStore s op index out source memory
  let p := paid b op 4
  let q := paid p op 4
  have c0 : s.host.gas.Credits (4 * op + (12 * op + rest)) := hc.mono (by omega)
  have h0 := paid_gas s op 4 (12 * op + rest) c0
  have c1 : b.host.gas.Credits (12 * op + rest) := by
    simpa only [b, byteStore, storeByte] using paid_credits s op 4 (12 * op + rest) c0
  have h1 : b.host.gas.burnt = s.host.gas.burnt + 4 * op ∧ b.host.gas.promises = s.host.gas.promises := h0
  have c1' : b.host.gas.Credits (4 * op + (8 * op + rest)) := c1.mono (by omega)
  have h2 : p.host.gas.burnt = b.host.gas.burnt + 4 * op ∧ p.host.gas.promises = b.host.gas.promises :=
    paid_gas b op 4 (8 * op + rest) c1'
  have c2 : p.host.gas.Credits (4 * op + (4 * op + rest)) := by
    have h := paid_credits b op 4 (8 * op + rest) c1'
    exact h.mono (by omega)
  have h3 : q.host.gas.burnt = p.host.gas.burnt + 4 * op ∧ q.host.gas.promises = p.host.gas.promises :=
    paid_gas p op 4 (4 * op + rest) c2
  have c3 : q.host.gas.Credits (4 * op + rest) := paid_credits p op 4 (4 * op + rest) c2
  have h4 := paid_gas q op 4 rest c3
  have hb : (prefixStore s op index out source memory).host.gas.burnt = q.host.gas.burnt + 4 * op := h4.1
  have hp : (prefixStore s op index out source memory).host.gas.promises = q.host.gas.promises := h4.2
  exact ⟨by omega, hp.trans (h3.2.trans (h2.2.trans h1.2))⟩

attribute [local irreducible] prefixStore byteStore chargedStore

/-- The positive loop burns18 units per byte except the untaken final
backedge, retaining exactly the original promise reservations. The zero case
is the unchanged store. -/
theorem loopStore_gas (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count rest : Nat)
    (hc : s.host.gas.Credits ((18 * count - 1) * op + rest)) :
    (loopStore s op index out source memory count).host.gas.burnt =
      s.host.gas.burnt + (18 * count - 1) * op ∧
    (loopStore s op index out source memory count).host.gas.promises = s.host.gas.promises := by
  induction count generalizing s memory out source with
  | zero =>
    have hz : (18 * 0 - 1) * op = 0 := by omega
    rw [hz, Nat.add_zero]
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    have budget : (18 * (n + 1) - 1) * op = 16 * op + ((if n = 0 then 1 else 2) * op + (18 * n - 1) * op) := by
      by_cases hn : n = 0
      · subst n; simp; omega
      · simp only [hn, ↓reduceIte]
        exact loop_cost_step op n (by omega)
    have c0 : s.host.gas.Credits (16 * op + ((if n = 0 then 1 else 2) * op + ((18 * n - 1) * op + rest))) := by
      convert hc using 1; omega
    have hpref := prefixStore_gas s op index out source memory _ c0
    have cp := prefixStore_credits s op index out source memory _ c0
    have hb := GasCounter.burn_credits (prefixStore s op index out source memory).host.gas
      ((if n = 0 then 1 else 2) * op) ((18 * n - 1) * op + rest) cp
    let next := chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op)
    have cn : next.host.gas.Credits ((18 * n - 1) * op + rest) := by
      simpa only [next, chargedStore, chargeHost] using hb.2.2.2
    have hn : next.host.gas.burnt = (prefixStore s op index out source memory).host.gas.burnt +
        (if n = 0 then 1 else 2) * op := by
      simpa only [next, chargedStore, chargeHost] using hb.2.1
    have hnp : next.host.gas.promises = (prefixStore s op index out source memory).host.gas.promises := by
      simpa only [next, chargedStore, chargeHost] using hb.2.2.1
    have tail := ih next (out + 1) (source + 1) (writeByte memory out.toNat (readByteWord memory source.toNat)) cn
    rw [loopStore_succ]
    change (loopStore next op index (out + 1) (source + 1)
      (writeByte memory out.toNat (readByteWord memory source.toNat)) n).host.gas.burnt =
        s.host.gas.burnt + (18 * (n + 1) - 1) * op ∧ _
    exact ⟨by omega, tail.2.trans (hnp.trans hpref.2)⟩

end WNear.Proofs.UnwrapStateCopyGas
