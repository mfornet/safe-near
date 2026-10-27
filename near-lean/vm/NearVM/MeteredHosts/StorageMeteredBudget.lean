import NearVM.MeteredHosts.StoragePrepareBudget

/-!
# Budget replay of the complete metered storage-write wrapper

Precharges, used-gas synchronization, ordinary argument rejection and the
actual trie/raw/post-call invocation are composed here. Trie readiness consists
only of primitive facts at the low paid functional state. It is needed only
when the actual pre-invocation validator accepts the arguments.
-/
namespace Wasm.Near.MeteredHosts.StorageMeteredBudget
open Budget StorageMetered StoragePrepareBudget

/-- The actual precharged host view, including guest-visible used gas. -/
def paid (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) : HostStore NearState :=
  Output.paidStore st (applyCharges st.host
    (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr))).1

/-- Primitive fresh-key obligations, supplied only for the low paid state. -/
def FreshReady (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) : Prop :=
  ∃ key value initial looked,
    st.host.storageAccounting = some initial ∧
    getMemOrReg st keyPtr keyLen = some key ∧
    (∀ limit, st.host.config.maxStorageKeyLen = some limit → key.length ≤ limit) ∧
    _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey st.host.context.currentAccountId key) true = .ok (looked, none) ∧
    st.host.storage key = none ∧ getMemOrReg st valuePtr valueLen = some value ∧
    recordedStorageError st.host
      (looked.set (_root_.Near.TrieOverlay.contractKey st.host.context.currentAccountId key) value) = none

/-- Primitive replacement obligations, including the actual paid reference's
shared dereference. Neither a large-state replay nor a host callback is assumed. -/
def ReplaceReady (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) : Prop :=
  ∃ key value old initial looked fetched pointer,
    st.host.storageAccounting = some initial ∧
    getMemOrReg st keyPtr keyLen = some key ∧
    (∀ limit, st.host.config.maxStorageKeyLen = some limit → key.length ≤ limit) ∧
    _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey st.host.context.currentAccountId key) true = .ok (looked, some pointer) ∧
    st.host.storage key = some old ∧
    _root_.Near.TrieOverlay.dereference looked pointer = .ok (fetched, old) ∧
    getMemOrReg st valuePtr valueLen = some value ∧
    recordedStorageError st.host
      (fetched.set (_root_.Near.TrieOverlay.contractKey st.host.context.currentAccountId key) value) = none

def Ready (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) : Prop :=
  FreshReady st keyLen keyPtr valueLen valuePtr ∨ ReplaceReady st keyLen keyPtr valueLen valuePtr

private theorem paid_frame (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) :
    (paid st keyLen keyPtr valueLen valuePtr).host.logs = st.host.logs ∧
    (paid st keyLen keyPtr valueLen valuePtr).host.lastExecutionIssue = st.host.lastExecutionIssue := by
  have hf := applyCharges_frame st.host _ (StorageBudget.plan_burnsOnly st keyLen keyPtr valueLen valuePtr)
  have hl := congrArg NearState.logs hf
  have hi := congrArg NearState.lastExecutionIssue hf
  exact ⟨hl, hi⟩

/-- Ordinary read/length rejection is identical at related paid states. -/
theorem preInvoke_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    preInvokeError "storage_write" small (args keyLen keyPtr valueLen valuePtr) =
      preInvokeError "storage_write" large (args keyLen keyPtr valueLen valuePtr) := by
  have hex : ∃ plan, storageMutationPlan? "storage_write" small
      (args keyLen keyPtr valueLen valuePtr) = some plan := by
    simp only [storageMutationPlan?, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
      show ("storage_write" != "storage_write" && "storage_write" != "storage_remove") = false by decide,
      show ("storage_write" == "storage_write") = true by decide, Bool.false_eq_true, ↓reduceIte]
    repeat' first | exact ⟨_, rfl⟩ | split
  obtain ⟨plan, hp⟩ := hex
  have hl := (StorageBudget.mutationPlan_eq h keyLen keyPtr valueLen valuePtr).symm.trans hp
  simp only [preInvokeError, invocationArgumentError, hp, hl]
  cases plan.error <;> simp [allocatesPromise, functionCallInputError, functionCallInputs?]

/-- Exact operational wrapper equation after the non-view check. -/
theorem metered_eq (extra : Nat) (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (hview : st.host.context.isView = false) :
    (metered extra "storage_write" storageWriteFn).invoke st (args keyLen keyPtr valueLen valuePtr) =
      match (applyCharges st.host
        (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr))).2 with
      | some error => trapWith (paid st keyLen keyPtr valueLen valuePtr) error
      | none =>
        match preInvokeError "storage_write" (paid st keyLen keyPtr valueLen valuePtr)
          (args keyLen keyPtr valueLen valuePtr) with
        | some error => trapWith (paid st keyLen keyPtr valueLen valuePtr) error
        | none => invokeStorageCall extra "storage_write" storageWriteFn
            (paid st keyLen keyPtr valueLen valuePtr) (args keyLen keyPtr valueLen valuePtr) := by
  simp only [metered, show deprecatedRuntimeHost "storage_write" = false by decide,
    hview, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  unfold paid Output.paidStore
  cases applyCharges st.host (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr))
  rfl

/-- Every complete non-view storage-write exit retains logs, including an
ordinary validator error, trie issue, inner gas failure or post-call gas stop. -/
theorem metered_logs (extra : Nat) (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (hview : st.host.context.isView = false) :
    (resultStore ((metered extra "storage_write" storageWriteFn).invoke st
      (args keyLen keyPtr valueLen valuePtr))).host.logs = st.host.logs := by
  rw [metered_eq extra st keyLen keyPtr valueLen valuePtr hview]
  cases (applyCharges st.host (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr))).2 with
  | some error => exact (paid_frame st keyLen keyPtr valueLen valuePtr).1
  | none =>
    cases preInvokeError "storage_write" (paid st keyLen keyPtr valueLen valuePtr)
      (args keyLen keyPtr valueLen valuePtr) with
    | some error => exact (paid_frame st keyLen keyPtr valueLen valuePtr).1
    | none =>
      exact (StoragePrepareBudget.invoke_logs extra _ keyLen keyPtr valueLen valuePtr).trans
        (paid_frame st keyLen keyPtr valueLen valuePtr).1

private theorem ready_replay (extra : Nat) {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (hr : Ready small keyLen keyPtr valueLen valuePtr)
    (hissue : small.host.lastExecutionIssue = none) :
    HostReplays
      (invokeStorageCall extra "storage_write" storageWriteFn small (args keyLen keyPtr valueLen valuePtr))
      (invokeStorageCall extra "storage_write" storageWriteFn large (args keyLen keyPtr valueLen valuePtr)) := by
  rcases hr with hf | hr
  · rcases hf with ⟨key, value, initial, looked, ha, hk, hl, hlookup, hs, hv, hp⟩
    exact fresh_invoke_replay extra h keyLen keyPtr valueLen valuePtr key value initial looked
      ha hk hl hlookup hs hv hp hissue
  · rcases hr with ⟨key, value, old, initial, looked, fetched, pointer, ha, hk, hl, hlookup, hs, hfetch, hv, hp⟩
    exact replace_invoke_replay extra h keyLen keyPtr valueLen valuePtr key value old initial looked fetched pointer
      ha hk hl hlookup hs hfetch hv hp hissue

private theorem error_below {small large : HostStore NearState} (h : StoreBelow small large)
    (error : HostError) : StoreBelow {small with host := {small.host with lastError := some error}}
      {large with host := {large.host with lastError := some error}} := by
  have hf := congrArg (fun st : NearState => {st with lastError := some error}) h.host.fields
  exact ⟨h.mem, by simpa only [functional] using hf, h.host.gas⟩

/-- Replay of the actual complete metered discard-output storage write. The
first precharge, ordinary shared validation errors, both trie paths and every
inner/post-call low-gas stop are covered. Only local primitive readiness at
the low paid state is needed when its actual validator accepts the call. -/
theorem replay (extra : Nat) {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (hview : small.host.context.isView = false)
    (hready : preInvokeError "storage_write" (paid small keyLen keyPtr valueLen valuePtr)
      (args keyLen keyPtr valueLen valuePtr) = none → Ready (paid small keyLen keyPtr valueLen valuePtr)
        keyLen keyPtr valueLen valuePtr)
    (hissue : small.host.lastExecutionIssue = none) :
    HostReplays
      ((metered extra "storage_write" storageWriteFn).invoke small (args keyLen keyPtr valueLen valuePtr))
      ((metered extra "storage_write" storageWriteFn).invoke large (args keyLen keyPtr valueLen valuePtr)) := by
  have hlargeView : large.host.context.isView = false := (congrArg (·.isView) h.host.context).symm.trans hview
  have hs := metered_eq extra small keyLen keyPtr valueLen valuePtr hview
  have hl := metered_eq extra large keyLen keyPtr valueLen valuePtr hlargeView
  cases he : (applyCharges small.host
    (chargesBefore "storage_write" small (args keyLen keyPtr valueLen valuePtr))).2 with
  | some error =>
    have hf := StorageBudget.metered_precharge_failure extra small keyLen keyPtr valueLen valuePtr error hview he hissue
    refine Or.inr ⟨error, paid small keyLen keyPtr valueLen valuePtr, hf.2.1, hf.1, hf.2.2.2, ?_⟩
    exact hf.2.2.1.trans (h.host.logs.trans (metered_logs extra large keyLen keyPtr valueLen valuePtr hlargeView).symm)
  | none =>
    have hc := StorageBudget.precharge_below h keyLen keyPtr valueLen valuePtr he
    have hp : StoreBelow (paid small keyLen keyPtr valueLen valuePtr) (paid large keyLen keyPtr valueLen valuePtr) := hc.2
    have hfresh := (paid_frame small keyLen keyPtr valueLen valuePtr).2.trans hissue
    have hv := preInvoke_eq hp keyLen keyPtr valueLen valuePtr
    cases hvSmall : preInvokeError "storage_write" (paid small keyLen keyPtr valueLen valuePtr)
      (args keyLen keyPtr valueLen valuePtr) with
    | some error =>
      have hvLarge := hv.symm.trans hvSmall
      left
      rw [hs, hl]
      simp only [he, hc.1, hvSmall, hvLarge]
      exact .trapped error.message (error_below hp error)
    | none =>
      have hvLarge := hv.symm.trans hvSmall
      have hr := ready_replay extra hp keyLen keyPtr valueLen valuePtr (hready hvSmall) hfresh
      simpa only [hs, hl, he, hc.1, hvSmall, hvLarge] using hr

/-- A returning complete wrapper preserves issue freshness. Terminal
structured trie errors remain allowed and cannot satisfy the return equation. -/
theorem metered_return_issue (extra : Nat) (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (hview : st.host.context.isView = false)
    (values : List Value) (after : HostStore NearState)
    (hreturn : (metered extra "storage_write" storageWriteFn).invoke st
      (args keyLen keyPtr valueLen valuePtr) = .Return values after) :
    after.host.lastExecutionIssue = st.host.lastExecutionIssue := by
  rw [metered_eq extra st keyLen keyPtr valueLen valuePtr hview] at hreturn
  cases he : (applyCharges st.host (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr))).2 with
  | some error => simp only [he] at hreturn; cases hreturn
  | none =>
    simp only [he] at hreturn
    cases hp : preInvokeError "storage_write" (paid st keyLen keyPtr valueLen valuePtr)
      (args keyLen keyPtr valueLen valuePtr) with
    | some error => simp only [hp] at hreturn; cases hreturn
    | none =>
      simp only [hp] at hreturn
      exact (invoke_return_issue extra _ keyLen keyPtr valueLen valuePtr values after hreturn).trans
        (paid_frame st keyLen keyPtr valueLen valuePtr).2

end Wasm.Near.MeteredHosts.StorageMeteredBudget
