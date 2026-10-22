import Proofs.Safety

namespace Linkdrop

theorem empty_wf : empty.WF := by simp [empty, State.WF]

theorem empty_finite : empty.Finite := by
  exact ⟨[], by simp [empty]⟩

theorem finite_preserved {s : State} {e : Env} {c : Call} {out : Outcome}
    (hwf : s.WF) (hf : s.Finite) (h : step s e c = .ok out) : out.state.Finite := by
  obtain ⟨keys, hkeys⟩ := hf
  cases ht : Spec.touchedKey e c with
  | none =>
    refine ⟨keys, ?_⟩
    intro k hk
    rw [mapAuthorization s e c out k hwf h (by simp [ht])]
    exact hkeys k hk
  | some j =>
    refine ⟨j :: keys, ?_⟩
    intro k hk
    simp only [List.mem_cons, not_or] at hk
    have hkj : j ≠ k := by simpa [ne_comm] using hk.1
    have hkeys' : k ∉ keys := by simp_all
    rw [mapAuthorization s e c out k hwf h (by simp [ht, hkj])]
    exact hkeys k hkeys'

/-- Successful model executions with bounded, decoded inputs. Failed runtime
receipts, action execution, gas and scheduler transitions are not encoded here. -/
inductive Reachable : State → Prop
  | start : Reachable empty
  | next {s : State} {e : Env} {c : Call} {out : Outcome} :
      Reachable s → e.deposit ≤ maxAmount → c.WF →
      step s e c = .ok out → Reachable out.state

theorem reachable_invariants {s : State} (h : Reachable s) : s.WF ∧ s.Finite := by
  induction h with
  | start => exact ⟨empty_wf, empty_finite⟩
  | next _ hd hc hstep ih =>
    exact ⟨invPreserved _ _ _ _ ih.1 hd hc hstep, finite_preserved ih.1 ih.2 hstep⟩

end Linkdrop
