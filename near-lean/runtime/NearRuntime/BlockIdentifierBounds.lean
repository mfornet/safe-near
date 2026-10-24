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
theorem applyAttempt_identifier_bounds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (hstate : st.IdsBelowNext) (hincoming : ReceiptList.IdsBelow st.nextId incoming) :
    (applyAttempt cfg ap decoder st txs incoming).IdentifierBounds := by
  have hempty (bound : Nat) : ReceiptList.IdsBelow bound [] := by intro receipt hm; contradiction
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn (chunkTransactions cfg txs) _ _ : Id TransactionLoop) = txResult
  have htx : TransactionLoop.IdentifierInvariant st.nextId txResult := by
    rw [← ht]
    apply forIn_id_preserves _ _ _ (TransactionLoop.IdentifierInvariant st.nextId)
    · exact ⟨hstate, hempty _, hempty _, Nat.le_refl _, by intro result he; contradiction⟩
    · intro tx pass h
      cases hc : convertTransaction cfg ap pass.2.1 tx with
      | error error =>
        dsimp only
        cases hi : error.issue? with
        | some issue =>
          dsimp only
          exact ⟨h.state, h.localReceipts, h.outgoing, h.counter,
            by intro result he; cases he; exact ⟨hstate, hempty _⟩⟩
        | none =>
          dsimp only
          exact ⟨h.state, h.localReceipts, h.outgoing, h.counter, by intro result he; contradiction⟩
      | ok value =>
        obtain ⟨next, receipt, cost⟩ := value
        have hn := (convertTransaction_receipt_counter cfg ap pass.2.1 next tx receipt cost hc).2
        have hmono : pass.2.1.nextId ≤ next.nextId := by omega
        have hs := convertTransaction_idsBelowNext cfg ap pass.2.1 next tx receipt cost h.state hc
        have hr : ReceiptList.IdsBelow next.nextId [receipt] := by
          intro candidate hm
          have he := List.mem_singleton.mp hm
          subst candidate
          exact convertTransaction_receipt_idsBelowNext cfg ap pass.2.1 next tx receipt cost hc
        dsimp only
        split_ifs
        · exact ⟨hs, (h.localReceipts.mono hmono).append hr, h.outgoing.mono hmono,
            h.counter.trans hmono, by intro result he; contradiction⟩
        · exact ⟨hs, h.localReceipts.mono hmono, (h.outgoing.mono hmono).append hr,
            h.counter.trans hmono, by intro result he; contradiction⟩
  split
  · rename_i result he
    exact htx.returned result he
  · let queue := txResult.2.2.2.2.1 ++ txResult.2.1.delayed ++ incoming
    have hqueue : ReceiptList.IdsBelow txResult.2.1.nextId queue := by
      intro receipt hm id hid
      rcases List.mem_append.mp hm with hprior | hin
      · rcases List.mem_append.mp hprior with hlocal | hdelayed
        · exact htx.localReceipts receipt hlocal id hid
        · exact ((ChainState.idsBelowNext_iff _).mp htx.state).delayed receipt hdelayed id hid
      · exact (hincoming receipt hin id hid).trans_le htx.counter
    generalize hq : (forIn queue.zipIdx _ _ : Id ReceiptLoop) = result
    have hresult : ReceiptLoop.IdentifierInvariant queue result := by
      rw [← hq]
      apply forIn_id_preserves_mem _ _ _ (ReceiptLoop.IdentifierInvariant queue)
      · exact ⟨delayed_clear_idsBelowNext _ htx.state, htx.outgoing, hqueue,
          hempty _, hempty _, by intro returned he; contradiction⟩
      · intro entry hm pass h
        have hmember := List.fst_mem_of_mem_zipIdx hm
        have hsingle : ReceiptList.IdsBelow pass.2.1.nextId [entry.1] := by
          intro receipt he
          have heq := List.mem_singleton.mp he
          subst receipt
          exact h.queued entry.1 hmember
        by_cases hover : pass.2.2.2.2.2.2.2.2.2.2.1 = true
        · simp only [hover, ite_true]
          split_ifs
          · exact ⟨h.state, h.outgoing, h.queued, h.retained.append hsingle, h.appended,
              by intro returned he; contradiction⟩
          · exact ⟨h.state, h.outgoing, h.queued, h.retained, h.appended.append hsingle,
              by intro returned he; contradiction⟩
        · simp only [hover, Bool.false_eq_true, ite_false]
          cases hi : (processReceipt cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1).issue with
          | some issue =>
            dsimp only
            exact ⟨h.state, h.outgoing, h.queued, h.retained, h.appended,
              by intro returned he; cases he; exact ⟨hstate, hempty _⟩⟩
          | none =>
            dsimp only
            have hp := processReceipt_identifier_bounds cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1 h.state (h.queued entry.1 hmember)
            have hn := processReceipt_nextId_mono cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1
            have hout := (h.outgoing.mono hn).append hp.2
            cases hl : ap.gasLimit with
            | none =>
              simp only [hl] at hp hn hout
              exact ⟨hp.1, hout, h.queued.mono hn, h.retained.mono hn, h.appended.mono hn,
                by intro returned he; contradiction⟩
            | some limit =>
              simp only [hl] at hp hn hout
              dsimp only
              split_ifs <;> exact ⟨hp.1, hout, h.queued.mono hn, h.retained.mono hn, h.appended.mono hn,
                by intro returned he; contradiction⟩
    split
    · rename_i returned he
      exact hresult.returned returned he
    · refine ⟨?_, hresult.outgoing⟩
      have hs := (ChainState.idsBelowNext_iff result.2.1).mp hresult.state
      apply (ChainState.idsBelowNext_iff _).mpr
      exact ⟨hs.postponed, hs.pending, hs.routes, hs.received, hresult.retained.append hresult.appended⟩

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
