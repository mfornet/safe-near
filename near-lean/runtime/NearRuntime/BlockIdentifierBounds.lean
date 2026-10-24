import NearRuntime.ProcessorOutputIdentifierBounds

namespace Near
open Wasm.Near

/-- Bounds on external queues and public outgoing work. -/
def ReceiptList.IdsBelow (bound : Nat) (receipts : List Receipt) : Prop :=
  ∀ receipt ∈ receipts, ∀ id ∈ receipt.liveIds, id < bound

def ApplyResult.IdentifierBounds (result : ApplyResult) : Prop :=
  result.state.IdsBelowNext ∧ ReceiptList.IdsBelow result.state.nextId result.outgoing

theorem ReceiptList.IdsBelow.mono {before after : Nat} {receipts : List Receipt}
    (h : ReceiptList.IdsBelow before receipts) (hle : before ≤ after) : ReceiptList.IdsBelow after receipts := by
  intro receipt hm id hid
  exact (h receipt hm id hid).trans_le hle

theorem delayed_clear_idsBelowNext (st : ChainState) (h : st.IdsBelowNext) :
    ({ st with delayed := [] } : ChainState).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  exact ⟨h.postponed, h.pending, h.routes, h.received, by simp⟩

theorem delayed_append_idsBelowNext (st : ChainState) (receipt : Receipt) (h : st.IdsBelowNext)
    (hr : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    ({ st with delayed := st.delayed ++ [receipt] } : ChainState).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  refine ⟨h.postponed, h.pending, h.routes, h.received, ?_⟩
  intro candidate hm id hid
  rcases List.mem_append.mp hm with hold | hnew
  · exact h.delayed candidate hold id hid
  · have he := List.mem_singleton.mp hnew
    subst candidate
    exact hr id hid

/-- Preservation over the actual early-exit loop, with membership in its fixed
iteration domain available to the step proof. -/
theorem forIn_id_preserves_mem {α β : Type} (xs : List α) (initial : β)
    (step : α → β → Id (ForInStep β)) (P : β → Prop) (hinitial : P initial)
    (hstep : ∀ x ∈ xs, ∀ state, P state →
      match step x state with | .done next | .yield next => P next) :
    P (forIn xs initial step : Id β) := by
  induction xs generalizing initial with
  | nil => exact hinitial
  | cons x xs ih =>
    rw [List.forIn_cons]
    have hp := hstep x (by simp) initial hinitial
    cases he : step x initial with
    | done next => simpa only [he, bind, pure] using hp
    | yield next =>
      apply ih next (by simpa only [he, bind, pure] using hp)
      intro item hm state hs
      exact hstep item (by simp [hm]) state hs

theorem ReceiptList.IdsBelow.append {bound : Nat} {left right : List Receipt}
    (hl : ReceiptList.IdsBelow bound left) (hr : ReceiptList.IdsBelow bound right) :
    ReceiptList.IdsBelow bound (left ++ right) := by
  intro receipt hm id hid
  rcases List.mem_append.mp hm with h | h
  · exact hl receipt h id hid
  · exact hr receipt h id hid

structure TransactionLoop.IdentifierInvariant (lower : Nat) (pass : TransactionLoop) : Prop where
  state : pass.2.1.IdsBelowNext
  localReceipts : ReceiptList.IdsBelow pass.2.1.nextId pass.2.2.2.2.1
  outgoing : ReceiptList.IdsBelow pass.2.1.nextId pass.2.2.2.1
  counter : lower ≤ pass.2.1.nextId
  returned : ∀ result, pass.1 = some result → result.IdentifierBounds

structure ReceiptLoop.IdentifierInvariant (queue : List Receipt) (pass : ReceiptLoop) : Prop where
  state : pass.2.1.IdsBelowNext
  outgoing : ReceiptList.IdsBelow pass.2.1.nextId pass.2.2.2.1
  queued : ReceiptList.IdsBelow pass.2.1.nextId queue
  retained : ReceiptList.IdsBelow pass.2.1.nextId pass.2.2.2.2.2.2.2.1
  appended : ReceiptList.IdsBelow pass.2.1.nextId pass.2.2.2.2.2.2.2.2.1
  returned : ∀ result, pass.1 = some result → result.IdentifierBounds

/-- Both executable loops bound local/nonlocal transaction receipts, emitted
work and both delayed buffers. Atomic issues restore the initial bounds. -/
-- TODO(proof): adapt the cloned proof
theorem applyAttempt_identifier_bounds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (hstate : st.IdsBelowNext) (hincoming : ReceiptList.IdsBelow st.nextId incoming) :
    (applyAttempt cfg ap decoder st txs incoming).IdentifierBounds := by
  sorry

/-- The public atomic apply boundary preserves state and outgoing identifier
bounds even when the attempt is unsupported or incomplete. -/
theorem apply_identifier_bounds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (hstate : st.IdsBelowNext) (hincoming : ReceiptList.IdsBelow st.nextId incoming) :
    (apply cfg ap decoder st txs incoming).IdentifierBounds := by
  unfold apply
  dsimp only
  split
  · exact ⟨hstate, by intro receipt hm; contradiction⟩
  · exact applyAttempt_identifier_bounds cfg ap decoder st txs incoming hstate hincoming

end Near
