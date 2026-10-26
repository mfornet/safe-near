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
  exact ⟨h.postponed, h.pending, h.routes, h.received, by simp, h.yields⟩

theorem delayed_append_idsBelowNext (st : ChainState) (receipt : Receipt) (h : st.IdsBelowNext)
    (hr : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    ({ st with delayed := st.delayed ++ [receipt] } : ChainState).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  refine ⟨h.postponed, h.pending, h.routes, h.received, ?_, h.yields⟩
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

/-- Yield timeouts only allocate identifiers for the resume receipts they emit. -/
theorem resolveYieldTimeouts_bounds (ap : ApplyState) (limit : Option Nat) (used fuel : Nat) :
    ∀ (acc : ChainState × List Receipt × List ReceiptIdentityBirth),
      acc.1.IdsBelowNext → ReceiptList.IdsBelow acc.1.nextId acc.2.1 →
      (resolveYieldTimeouts ap limit used fuel acc).1.IdsBelowNext ∧
      ReceiptList.IdsBelow (resolveYieldTimeouts ap limit used fuel acc).1.nextId
        (resolveYieldTimeouts ap limit used fuel acc).2.1 := by
  induction fuel with
  | zero => intro acc h1 h2; exact ⟨h1, h2⟩
  | succ fuel ih =>
    rintro ⟨st, receipts, births⟩ h1 h2
    unfold resolveYieldTimeouts
    dsimp only at h1 h2 ⊢
    split
    · exact ⟨h1, h2⟩
    · split
      · split
        · exact ⟨h1, h2⟩
        · split
          · exact ⟨h1, h2⟩
          · split
            · apply ih
              · exact h1.of_frame rfl (Nat.le_add_right _ _)
              · intro receipt hm id hid
                simp only [ChainState.freshId, List.mem_append, List.mem_singleton] at hm ⊢
                rcases hm with hold | rfl
                · exact (h2 receipt hold id hid).trans (Nat.lt_succ_self _)
                · simp [Receipt.liveIds] at hid
                  omega
            · apply ih
              · exact h1
              · exact h2
      · exact ⟨h1, h2⟩

theorem resolveYieldTimeouts_nextId_mono (ap : ApplyState) (limit : Option Nat) (used fuel : Nat) :
    ∀ (acc : ChainState × List Receipt × List ReceiptIdentityBirth),
      acc.1.nextId ≤ (resolveYieldTimeouts ap limit used fuel acc).1.nextId := by
  induction fuel with
  | zero => intro acc; exact Nat.le_refl _
  | succ fuel ih =>
    rintro ⟨st, receipts, births⟩
    unfold resolveYieldTimeouts
    dsimp only
    split
    · exact Nat.le_refl _
    · split
      · split
        · exact Nat.le_refl _
        · split
          · exact Nat.le_refl _
          · split
            · refine Nat.le_trans ?_ (ih _)
              exact Nat.le_add_right _ 1
            · refine Nat.le_trans ?_ (ih _)
              exact Nat.le_refl _
      · exact Nat.le_refl _

theorem timeouts_identifier_bounds (ap : ApplyState) (limit : Option Nat) (used fuel : Nat) (st : ChainState)
    (outgoing retained appended : List Receipt) (hst : st.IdsBelowNext)
    (hout : ReceiptList.IdsBelow st.nextId outgoing) (hret : ReceiptList.IdsBelow st.nextId retained)
    (happ : ReceiptList.IdsBelow st.nextId appended) :
    ({ (resolveYieldTimeouts ap limit used fuel (st, [], [])).1 with
        delayed := retained ++ appended } : ChainState).IdsBelowNext ∧
    ReceiptList.IdsBelow (resolveYieldTimeouts ap limit used fuel (st, [], [])).1.nextId
      (outgoing ++ (resolveYieldTimeouts ap limit used fuel (st, [], [])).2.1) := by
  have hy := resolveYieldTimeouts_bounds ap limit used fuel (st, [], []) hst
    (by intro receipt hm; contradiction)
  have hn := resolveYieldTimeouts_nextId_mono ap limit used fuel (st, [], [])
  have hs := (ChainState.idsBelowNext_iff _).mp hy.1
  refine ⟨?_, (hout.mono hn).append hy.2⟩
  apply (ChainState.idsBelowNext_iff _).mpr
  exact ⟨hs.postponed, hs.pending, hs.routes, hs.received, (hret.append happ).mono hn, hs.yields⟩

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
          cases hi : (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1).issue with
          | some issue =>
            dsimp only
            exact ⟨h.state, h.outgoing, h.queued, h.retained, h.appended,
              by intro returned he; cases he; exact ⟨hstate, hempty _⟩⟩
          | none =>
            dsimp only
            have hp := processWithInstants_identifier_bounds cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1 h.state (h.queued entry.1 hmember)
            have hn := processWithInstants_nextId_mono cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1
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
    · exact timeouts_identifier_bounds ap ap.gasLimit _ _ result.2.1 _ _ _ hresult.state hresult.outgoing
        hresult.retained hresult.appended

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
