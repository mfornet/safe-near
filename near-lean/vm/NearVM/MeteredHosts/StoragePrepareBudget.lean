import NearVM.MeteredHosts.StorageBudget

/-!
# Storage trie phase replay, including inner gas stops

The fresh and replacement branch theorems execute the real lookup, reference
byte payment, dereference and node payment in their actual order. Primitive
trie facts are supplied once for the common functional state. A failed low
payment yields a protocol host error, retains the warmed trie and prior issue,
and has the same logs as the high phase, whatever that high phase does.
-/
namespace Wasm.Near.MeteredHosts.StoragePrepareBudget
open Budget StorageMetered

/-- Public storage preparation splices billing into the original host. Failed
billing keeps the paid promise count as well as its warmed accounting trie. -/
def failed (before : HostStore NearState) (paid : NearState)
    (trie : _root_.Near.TrieOverlay.State) : HostStore NearState :=
  {before with host := {before.host with
    storageAccounting := some trie
    gas := {before.host.gas with burnt := paid.gas.burnt, promises := paid.gas.promises}
    gasProfile := paid.gasProfile}}

local macro "unfold_storage_aux" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearVM.Metered 0) "Wasm") "Near") "prepareStorageCallAux"
  `(tactic| unfold $(Lean.mkIdent name))

set_option maxHeartbeats 1500000 in
/-- Exact low exit at the fresh-key node bill: the staged write and proof
check have not run, while lookup cache warming is retained. -/
theorem fresh_charge_error (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key : List UInt8)
    (initial looked : _root_.Near.TrieOverlay.State) (paid : NearState) (error : HostError)
    (haccounting : before.host.storageAccounting = some initial)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) true = .ok (looked, none))
    (hstorage : before.host.storage key = none)
    (hcharge : applyCharges (accounted before looked).host (trieCharges initial looked) = (paid, some error)) :
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) =
      (failed before paid looked, some (.hostError error)) := by
  have hf := applyCharges_frame (accounted before looked).host (trieCharges initial looked)
    (trieCharges_burnsOnly initial looked)
  rw [hcharge] at hf
  have ht := congrArg NearState.storageAccounting hf
  change paid.storageAccounting = some looked at ht
  simp only [accounted, trieCharges] at hcharge
  unfold prepareStorageCall
  unfold_storage_aux
  simp only [Id.run, pure, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_write" = true by decide,
    ↓reduceIte, haccounting, hkey]
  cases hlimit : before.host.config.maxStorageKeyLen with
  | none => simp [hlookup, hstorage, hcharge, ht, failed]
  | some limit =>
    simp only [Nat.not_lt_of_ge (hkeyLimit limit hlimit), ↓reduceIte]
    simp [hlookup, hstorage, hcharge, ht, failed]

set_option maxHeartbeats 1500000 in
/-- Exact replacement stop at old-value byte billing. Dereference and node
billing have not run, so the final accounting trie is exactly `looked`. -/
theorem replace_value_error (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key old : List UInt8)
    (initial looked : _root_.Near.TrieOverlay.State) (pointer : _root_.Near.TrieOverlay.ValuePointer)
    (paid : NearState) (error : HostError)
    (haccounting : before.host.storageAccounting = some initial)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) true = .ok (looked, some pointer))
    (hstorage : before.host.storage key = some old)
    (hcharge : applyCharges (accounted before looked).host (evictedCharges pointer) = (paid, some error)) :
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) =
      (failed before paid looked, some (.hostError error)) := by
  have hf := applyCharges_frame (accounted before looked).host (evictedCharges pointer)
    (evictedCharges_burnsOnly pointer)
  rw [hcharge] at hf
  have ht := congrArg NearState.storageAccounting hf
  change paid.storageAccounting = some looked at ht
  simp only [accounted, evictedCharges] at hcharge
  unfold prepareStorageCall
  unfold_storage_aux
  simp only [Id.run, pure, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_write" = true by decide,
    ↓reduceIte, haccounting, hkey]
  cases hlimit : before.host.config.maxStorageKeyLen with
  | none => simp [hlookup, hstorage, hcharge, ht, failed]
  | some limit =>
    simp only [Nat.not_lt_of_ge (hkeyLimit limit hlimit), ↓reduceIte]
    simp [hlookup, hstorage, hcharge, ht, failed]

set_option maxHeartbeats 1500000 in
/-- Exact replacement stop at node billing after the paid dereference. The
fetched cache state survives, but the new write has not yet been staged. -/
theorem replace_node_error (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key old : List UInt8)
    (initial looked fetched : _root_.Near.TrieOverlay.State)
    (pointer : _root_.Near.TrieOverlay.ValuePointer) (valuePaid nodePaid : NearState) (error : HostError)
    (haccounting : before.host.storageAccounting = some initial)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) true = .ok (looked, some pointer))
    (hstorage : before.host.storage key = some old)
    (hvalueCharge : applyCharges (accounted before looked).host (evictedCharges pointer) = (valuePaid, none))
    (hfetch : _root_.Near.TrieOverlay.dereference looked pointer = .ok (fetched, old))
    (hnodeCharge : applyCharges {valuePaid with storageAccounting := some fetched}
      (trieCharges initial fetched) = (nodePaid, some error)) :
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) =
      (failed before nodePaid fetched, some (.hostError error)) := by
  have hf := applyCharges_frame {valuePaid with storageAccounting := some fetched} (trieCharges initial fetched)
    (trieCharges_burnsOnly initial fetched)
  rw [hnodeCharge] at hf
  have ht := congrArg NearState.storageAccounting hf
  change nodePaid.storageAccounting = some fetched at ht
  simp only [accounted, evictedCharges] at hvalueCharge
  simp only [trieCharges] at hnodeCharge
  unfold prepareStorageCall
  unfold_storage_aux
  simp only [Id.run, pure, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_write" = true by decide,
    ↓reduceIte, haccounting, hkey]
  cases hlimit : before.host.config.maxStorageKeyLen with
  | none => simp [hlookup, hstorage, hvalueCharge, hfetch, hnodeCharge, ht, failed]
  | some limit =>
    simp only [Nat.not_lt_of_ge (hkeyLimit limit hlimit), ↓reduceIte]
    simp [hlookup, hstorage, hvalueCharge, hfetch, hnodeCharge, ht, failed]

/-- The runner-relevant local outcomes of an actual storage preparation. -/
def Replays (small large : HostStore NearState × Option FunctionCallError) : Prop :=
  (StoreBelow small.1 large.1 ∧ small.2 = large.2) ∨
  ∃ error, (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧ small.2 = some (.hostError error) ∧
    small.1.host.lastExecutionIssue = none ∧ small.1.host.logs = large.1.host.logs

private theorem gas_stop {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (error : HostError)
    (hgas : error = .gasLimitExceeded ∨ error = .gasExceeded)
    (herr : (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr)).2 = some (.hostError error))
    (hissue : small.host.lastExecutionIssue = none) :
    Replays (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr))
      (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)) := by
  have hs := StorageBudget.prepare_frame small keyLen keyPtr valueLen valuePtr
  have hl := StorageBudget.prepare_frame large keyLen keyPtr valueLen valuePtr
  exact Or.inr ⟨error, hgas, herr, hs.2.trans hissue, hs.1.trans (h.host.logs.trans hl.1.symm)⟩

/-- Complete fresh-key branch replay, including its inner gas failure. The
lookup and final proof obligation belong to the shared functional trie state. -/
theorem fresh_replay {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (initial looked : _root_.Near.TrieOverlay.State)
    (haccounting : small.host.storageAccounting = some initial)
    (hkey : getMemOrReg small keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, small.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) true = .ok (looked, none))
    (hstorage : small.host.storage key = none)
    (hvalue : getMemOrReg small valuePtr valueLen = some value)
    (hproof : recordedStorageError small.host
      (looked.set (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) value) = none)
    (hissue : small.host.lastExecutionIssue = none) :
    Replays (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr))
      (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)) := by
  cases he : (applyCharges (accounted small looked).host (trieCharges initial looked)).2 with
  | none =>
    have hs := StorageBudget.prepare_fresh_below h keyLen keyPtr valueLen valuePtr key value initial looked
      haccounting hkey hkeyLimit hlookup hstorage he hvalue hproof
    exact Or.inl ⟨hs.2.2, hs.1.trans hs.2.1.symm⟩
  | some error =>
    have hs := fresh_charge_error small keyLen keyPtr valueLen valuePtr key initial looked _ error
      haccounting hkey hkeyLimit hlookup hstorage (Prod.ext rfl he)
    exact gas_stop h keyLen keyPtr valueLen valuePtr error
      (applyCharges_error_is_gas _ _ (trieCharges_burnsOnly initial looked) he)
      (congrArg Prod.snd hs) hissue

/-- Complete replacement branch replay in its actual two-payment order. Low
reference-byte failure precedes dereference; low node failure retains `fetched`.
The same lookup/dereference facts suffice at the larger budget. -/
theorem replace_replay {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value old : List UInt8)
    (initial looked fetched : _root_.Near.TrieOverlay.State)
    (pointer : _root_.Near.TrieOverlay.ValuePointer)
    (haccounting : small.host.storageAccounting = some initial)
    (hkey : getMemOrReg small keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, small.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) true = .ok (looked, some pointer))
    (hstorage : small.host.storage key = some old)
    (hfetch : _root_.Near.TrieOverlay.dereference looked pointer = .ok (fetched, old))
    (hvalue : getMemOrReg small valuePtr valueLen = some value)
    (hproof : recordedStorageError small.host
      (fetched.set (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) value) = none)
    (hissue : small.host.lastExecutionIssue = none) :
    Replays (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr))
      (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)) := by
  cases hv : (applyCharges (accounted small looked).host (evictedCharges pointer)).2 with
  | some error =>
    have hs := replace_value_error small keyLen keyPtr valueLen valuePtr key old initial looked pointer _ error
      haccounting hkey hkeyLimit hlookup hstorage (Prod.ext rfl hv)
    exact gas_stop h keyLen keyPtr valueLen valuePtr error
      (applyCharges_error_is_gas _ _ (evictedCharges_burnsOnly pointer) hv)
      (congrArg Prod.snd hs) hissue
  | none =>
    cases hn : (applyCharges
      {(applyCharges (accounted small looked).host (evictedCharges pointer)).1 with storageAccounting := some fetched}
      (trieCharges initial fetched)).2 with
    | some error =>
      have hs := replace_node_error small keyLen keyPtr valueLen valuePtr key old initial looked fetched pointer _ _ error
        haccounting hkey hkeyLimit hlookup hstorage (Prod.ext rfl hv) hfetch (Prod.ext rfl hn)
      exact gas_stop h keyLen keyPtr valueLen valuePtr error
        (applyCharges_error_is_gas _ _ (trieCharges_burnsOnly initial fetched) hn)
        (congrArg Prod.snd hs) hissue
    | none =>
      have hs := StorageBudget.prepare_replace_below h keyLen keyPtr valueLen valuePtr key value old initial looked fetched pointer
        haccounting hkey hkeyLimit hlookup hstorage hfetch hv hn hvalue hproof
      exact Or.inl ⟨hs.2.2, hs.1.trans hs.2.1.symm⟩

/-- Concrete host exits after the real preparation, preserving exact gas
markers and retaining log equality even when the high call completes a write. -/
def HostReplays (small large : HostResult NearState) : Prop :=
  ResultBelow small large ∨
  ∃ error after, (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧
    small = trapWith after error ∧ after.host.lastExecutionIssue = none ∧
    after.host.logs = (resultStore large).host.logs

private def phaseExit (extra : Nat) (keyLen keyPtr valueLen valuePtr : UInt64)
    (after : HostStore NearState) : Option FunctionCallError → HostResult NearState
  | some (.hostError error) => trapWith after error
  | some (.executionIssue issue) =>
    .Trap {after with host := {after.host with lastExecutionIssue := some issue}} issue.message
  | some error => .Trap after error.message
  | none => finishMeteredCall extra "storage_write" after (args keyLen keyPtr valueLen valuePtr)
      (storageWriteFn.invoke after (args keyLen keyPtr valueLen valuePtr))

private theorem invoke_eq (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    invokeStorageCall extra "storage_write" storageWriteFn before (args keyLen keyPtr valueLen valuePtr) =
      phaseExit extra keyLen keyPtr valueLen valuePtr
        (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).1
        (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).2 := by
  unfold invokeStorageCall
  cases prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)
  rfl

private theorem phaseExit_logs (extra : Nat) (after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (error : Option FunctionCallError) :
    (resultStore (phaseExit extra keyLen keyPtr valueLen valuePtr after error)).host.logs = after.host.logs := by
  cases error with
  | none => exact (StorageBudget.raw_finish_frame extra after keyLen keyPtr valueLen valuePtr).1
  | some error => cases error <;> rfl

private theorem error_below {small large : HostStore NearState} (h : StoreBelow small large)
    (error : HostError) : StoreBelow {small with host := {small.host with lastError := some error}}
      {large with host := {large.host with lastError := some error}} := by
  have hf := congrArg (fun st : NearState => {st with lastError := some error}) h.host.fields
  exact ⟨h.mem, by simpa only [functional] using hf, h.host.gas⟩

private theorem issue_below {small large : HostStore NearState} (h : StoreBelow small large)
    (issue : ExecutionIssue) :
    StoreBelow {small with host := {small.host with lastExecutionIssue := some issue}}
      {large with host := {large.host with lastExecutionIssue := some issue}} := by
  have hf := congrArg (fun st : NearState => {st with lastExecutionIssue := some issue}) h.host.fields
  exact ⟨h.mem, by simpa only [functional] using hf, h.host.gas⟩

/-- Operational composition with the actual raw host and post-call billing.
The concrete `fresh_replay` and `replace_replay` above discharge its phase
premise; no hypothesis about the host implementation itself is needed. -/
theorem invoke_from_replay (extra : Nat) {small large : HostStore NearState}
    (keyLen keyPtr valueLen valuePtr : UInt64)
    (hr : Replays (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr))
      (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)))
    (hissue : small.host.lastExecutionIssue = none) :
    HostReplays
      (invokeStorageCall extra "storage_write" storageWriteFn small (args keyLen keyPtr valueLen valuePtr))
      (invokeStorageCall extra "storage_write" storageWriteFn large (args keyLen keyPtr valueLen valuePtr)) := by
  rw [invoke_eq, invoke_eq]
  rcases hr with ⟨hafter, heq⟩ | ⟨error, hgas, herr, hfresh, hlogs⟩
  · have hfresh := (StorageBudget.prepare_frame small keyLen keyPtr valueLen valuePtr).2.trans hissue
    rw [← heq]
    cases he : (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr)).2 with
    | none => exact StorageBudget.raw_finish_replay extra hafter keyLen keyPtr valueLen valuePtr hfresh
    | some error =>
      left
      cases error with
      | hostError error => exact .trapped error.message (error_below hafter error)
      | executionIssue issue => exact .trapped issue.message (issue_below hafter issue)
      | compilationError message => exact .trapped _ hafter
      | linkError message => exact .trapped _ hafter
      | methodResolveError error => exact .trapped _ hafter
      | wasmTrap error => exact .trapped _ hafter
      | internal message => exact .trapped _ hafter
      | prepareError error => exact .trapped _ hafter
  · right
    refine ⟨error, _, hgas, ?_, hfresh, ?_⟩
    · rw [herr]
      rfl
    · exact hlogs.trans (phaseExit_logs extra _ keyLen keyPtr valueLen valuePtr _).symm

/-- The concrete fresh-key lookup, inner payment, write and post-call payment
replay as one actual `invokeStorageCall`, including either low gas stop. -/
theorem fresh_invoke_replay (extra : Nat) {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (initial looked : _root_.Near.TrieOverlay.State)
    (haccounting : small.host.storageAccounting = some initial)
    (hkey : getMemOrReg small keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, small.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) true = .ok (looked, none))
    (hstorage : small.host.storage key = none)
    (hvalue : getMemOrReg small valuePtr valueLen = some value)
    (hproof : recordedStorageError small.host
      (looked.set (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) value) = none)
    (hissue : small.host.lastExecutionIssue = none) :
    HostReplays
      (invokeStorageCall extra "storage_write" storageWriteFn small (args keyLen keyPtr valueLen valuePtr))
      (invokeStorageCall extra "storage_write" storageWriteFn large (args keyLen keyPtr valueLen valuePtr)) :=
  invoke_from_replay extra keyLen keyPtr valueLen valuePtr
    (fresh_replay h keyLen keyPtr valueLen valuePtr key value initial looked
      haccounting hkey hkeyLimit hlookup hstorage hvalue hproof hissue) hissue

/-- Replacement lookup, old-value bill, dereference, node bill, functional write
and final bill compose at the actual host invocation boundary. -/
theorem replace_invoke_replay (extra : Nat) {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value old : List UInt8)
    (initial looked fetched : _root_.Near.TrieOverlay.State)
    (pointer : _root_.Near.TrieOverlay.ValuePointer)
    (haccounting : small.host.storageAccounting = some initial)
    (hkey : getMemOrReg small keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, small.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) true = .ok (looked, some pointer))
    (hstorage : small.host.storage key = some old)
    (hfetch : _root_.Near.TrieOverlay.dereference looked pointer = .ok (fetched, old))
    (hvalue : getMemOrReg small valuePtr valueLen = some value)
    (hproof : recordedStorageError small.host
      (fetched.set (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) value) = none)
    (hissue : small.host.lastExecutionIssue = none) :
    HostReplays
      (invokeStorageCall extra "storage_write" storageWriteFn small (args keyLen keyPtr valueLen valuePtr))
      (invokeStorageCall extra "storage_write" storageWriteFn large (args keyLen keyPtr valueLen valuePtr)) :=
  invoke_from_replay extra keyLen keyPtr valueLen valuePtr
    (replace_replay h keyLen keyPtr valueLen valuePtr key value old initial looked fetched pointer
      haccounting hkey hkeyLimit hlookup hstorage hfetch hvalue hproof hissue) hissue

/-- The whole actual storage invocation retains logs even on lookup,
dereference and proof errors, as well as every gas stop. -/
theorem invoke_logs (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    (resultStore (invokeStorageCall extra "storage_write" storageWriteFn before
      (args keyLen keyPtr valueLen valuePtr))).host.logs = before.host.logs := by
  rw [invoke_eq, phaseExit_logs]
  exact (StorageBudget.prepare_frame before keyLen keyPtr valueLen valuePtr).1

/-- An actual returning storage call preserves issue freshness. Structured
trie issues take terminal trap branches, so no assumption excludes them here. -/
theorem invoke_return_issue (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (values : List Value) (after : HostStore NearState)
    (hreturn : invokeStorageCall extra "storage_write" storageWriteFn before
      (args keyLen keyPtr valueLen valuePtr) = .Return values after) :
    after.host.lastExecutionIssue = before.host.lastExecutionIssue := by
  rw [invoke_eq] at hreturn
  cases he : (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).2 with
  | some error =>
    rw [he] at hreturn
    cases error <;> cases hreturn
  | none =>
    rw [he] at hreturn
    have hf := (StorageBudget.raw_finish_frame extra
      (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).1
      keyLen keyPtr valueLen valuePtr).2
    change finishMeteredCall extra "storage_write"
      (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).1
      (args keyLen keyPtr valueLen valuePtr)
      (storageWriteFn.invoke (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).1
        (args keyLen keyPtr valueLen valuePtr)) = .Return values after at hreturn
    rw [hreturn] at hf
    exact hf.trans (StorageBudget.prepare_frame before keyLen keyPtr valueLen valuePtr).2

end Wasm.Near.MeteredHosts.StoragePrepareBudget
