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

/-- Both actual block loops preserve routing bounds and establish bounds for
all outgoing work. Local transaction receipts, prior delayed work and external
incoming receipts are tracked through every deferral, execution and early exit. -/
theorem applyAttempt_identifier_bounds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (hstate : st.IdsBelowNext) (hincoming : ReceiptList.IdsBelow st.nextId incoming) :
    (applyAttempt cfg ap decoder st txs incoming).IdentifierBounds := by
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn txs _ _ : Id (ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat)) = txResult
  have htx : txResult.1.IdsBelowNext ∧ ReceiptList.IdsBelow txResult.1.nextId txResult.2.2.1 ∧
      st.nextId ≤ txResult.1.nextId := by
    rw [← ht]
    refine forIn_id_preserves txs (st, [], [], 0, 0) _
      (fun s : ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat =>
        s.1.IdsBelowNext ∧ ReceiptList.IdsBelow s.1.nextId s.2.2.1 ∧ st.nextId ≤ s.1.nextId)
      ⟨hstate, by intro receipt hm; contradiction, Nat.le_refl _⟩ ?_
    intro tx state hs
    cases hc : convertTransaction cfg ap state.1 tx with
    | error error => simpa only [hc] using hs
    | ok value =>
      obtain ⟨next, receipt, cost⟩ := value
      have hn := (convertTransaction_receipt_counter cfg ap state.1 next tx receipt cost hc).2
      have hmono : state.1.nextId ≤ next.nextId := by omega
      simp only
      refine ⟨convertTransaction_idsBelowNext cfg ap state.1 next tx receipt cost hs.1 hc, ?_, hs.2.2.trans hmono⟩
      intro candidate hm id hid
      rcases List.mem_append.mp hm with hold | hnew
      · exact (hs.2.1 candidate hold id hid).trans_le hmono
      · have he := List.mem_singleton.mp hnew
        subst candidate
        exact convertTransaction_receipt_idsBelowNext cfg ap state.1 next tx receipt cost hc id hid
  let queue := txResult.2.2.1 ++ txResult.1.delayed ++ incoming
  have hqueue : ReceiptList.IdsBelow txResult.1.nextId queue := by
    intro receipt hm id hid
    rcases List.mem_append.mp hm with hprior | hin
    · rcases List.mem_append.mp hprior with hlocal | hdelayed
      · exact htx.2.1 receipt hlocal id hid
      · exact ((ChainState.idsBelowNext_iff _).mp htx.1).delayed receipt hdelayed id hid
    · exact (hincoming receipt hin id hid).trans_le htx.2.2
  generalize hq : (forIn queue _ _ : Id (Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool)) = result
  have hresult : result.2.1.IdsBelowNext ∧ ReceiptList.IdsBelow result.2.1.nextId result.2.2.2.1 ∧
      ReceiptList.IdsBelow result.2.1.nextId queue ∧
      (∀ returned, result.1 = some returned → returned.IdentifierBounds) := by
    rw [← hq]
    apply forIn_id_preserves_mem _ _ _
      (fun s : Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool =>
        s.2.1.IdsBelowNext ∧ ReceiptList.IdsBelow s.2.1.nextId s.2.2.2.1 ∧
        ReceiptList.IdsBelow s.2.1.nextId queue ∧ ∀ returned, s.1 = some returned → returned.IdentifierBounds)
    · exact ⟨delayed_clear_idsBelowNext _ htx.1, by intro receipt hm; contradiction,
        hqueue, by intro returned he; contradiction⟩
    · intro receipt hmem state hs
      by_cases hover : state.2.2.2.2.2.2.2 = true
      · simp only [hover, ite_true]
        exact ⟨delayed_append_idsBelowNext _ receipt hs.1 (hs.2.2.1 receipt hmem),
          hs.2.1, hs.2.2.1, by intro returned he; contradiction⟩
      · simp only [hover, Bool.false_eq_true, ite_false]
        cases hi : (processReceipt cfg ap decoder state.2.1 receipt).issue with
        | some issue =>
          simp only
          refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
          intro returned he
          cases he
          exact ⟨hstate, by intro candidate hm; contradiction⟩
        | none =>
          simp only
          have hp := processReceipt_identifier_bounds cfg ap decoder state.2.1 receipt hs.1 (hs.2.2.1 receipt hmem)
          have hn := processReceipt_nextId_mono cfg ap decoder state.2.1 receipt
          have hout : ReceiptList.IdsBelow (processReceipt cfg ap decoder state.2.1 receipt).state.nextId
              (state.2.2.2.1 ++ (processReceipt cfg ap decoder state.2.1 receipt).receipts) := by
            intro candidate hm id hid
            rcases List.mem_append.mp hm with hold | hnew
            · exact (hs.2.1 candidate hold id hid).trans_le hn
            · exact hp.2 candidate hnew id hid
          have hkeep := hs.2.2.1.mono hn
          cases hl : ap.gasLimit with
          | none => exact ⟨hp.1, hout, hkeep, by intro returned he; contradiction⟩
          | some limit =>
            simp only
            split_ifs <;> exact ⟨hp.1, hout, hkeep, by intro returned he; contradiction⟩
  split
  · rename_i returned he
    exact hresult.2.2.2 returned he
  · exact ⟨hresult.1, hresult.2.1⟩

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
