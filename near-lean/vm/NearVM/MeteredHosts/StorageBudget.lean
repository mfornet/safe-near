import NearVM.MeteredHosts.StorageMetered
import NearVM.MeteredHosts.ReturnBudget

/-!
# Local budget compatibility for storage writes

These phase lemmas use the actual ordered trie operations and charges. They
cover arbitrary key/value spans with the discarded evicted-value register.
Functional state includes the full guest-visible context, storage, trie and
proof observer; only internal billing state is allowed to vary.
-/
namespace Wasm.Near.MeteredHosts.StorageBudget
open Budget StorageMetered

/-- The storage mutation validator and precharge plan observe no internal gas
limit or billing profile. This includes invalid spans and rejected lengths. -/
theorem mutationPlan_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    storageMutationPlan? "storage_write" small (args keyLen keyPtr valueLen valuePtr) =
      storageMutationPlan? "storage_write" large (args keyLen keyPtr valueLen valuePtr) := by
  have hr := congrArg NearState.registers h.host.fields
  have hs := congrArg NearState.storage h.host.fields
  have ht := congrArg NearState.storageAccounting h.host.fields
  simp only [functional] at hr hs ht
  simp [storageMutationPlan?, args, argU64, readSpan, storageValueCharges,
    ReturnBudget.read_eq h keyLen keyPtr, ReturnBudget.read_eq h valueLen valuePtr,
    h.host.config, hr, hs, ht]

private theorem plan_exists (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) :
    ∃ plan, storageMutationPlan? "storage_write" st (args keyLen keyPtr valueLen valuePtr) = some plan := by
  simp only [storageMutationPlan?, args, argU64, List.getElem?_cons_zero,
    List.getElem?_cons_succ, show ("storage_write" != "storage_write" && "storage_write" != "storage_remove") = false by decide,
    show ("storage_write" == "storage_write") = true by decide, Bool.false_eq_true, ↓reduceIte]
  repeat' first | exact ⟨_, rfl⟩ | split

/-- Pre-call storage billing is the same concrete charge sequence. -/
theorem plan_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    chargesBefore "storage_write" small (args keyLen keyPtr valueLen valuePtr) =
      chargesBefore "storage_write" large (args keyLen keyPtr valueLen valuePtr) := by
  obtain ⟨plan, hplan⟩ := plan_exists small keyLen keyPtr valueLen valuePtr
  have hlarge := (mutationPlan_eq h keyLen keyPtr valueLen valuePtr).symm.trans hplan
  simp only [chargesBefore, hplan, hlarge]

private theorem error_below {small large : NearState} (h : HostBelow small large)
    (error : HostError) : HostBelow {small with lastError := some error} {large with lastError := some error} := by
  have hf := congrArg (fun st : NearState => {st with lastError := some error}) h.fields
  exact ⟨by simpa only [functional] using hf, h.gas⟩

theorem written_below {small large : HostStore NearState} (h : StoreBelow small large)
    (key value : List UInt8) : StoreBelow (written small key value) (written large key value) := by
  have hf := congrArg (fun st : NearState => (st.setStorage key value).invalidateIterators) h.host.fields
  refine ⟨h.mem, ?_, h.host.gas⟩
  change functional ((small.host.setStorage key value).invalidateIterators) =
    functional ((large.host.setStorage key value).invalidateIterators)
  exact hf


/-- The functional discard-output write matches, including view prohibition,
invalid reads and both length failures. No valid-input premise is required. -/
theorem raw_below {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    ResultBelow (storageWriteFn.invoke small (args keyLen keyPtr valueLen valuePtr))
      (storageWriteFn.invoke large (args keyLen keyPtr valueLen valuePtr)) := by
  have hview : small.host.context.isView = large.host.context.isView := congrArg (·.isView) h.host.context
  cases hv : small.host.context.isView with
  | true =>
    have hl := hview.symm.trans hv
    simp only [storageWriteFn, disallowInView, hv, hl, ↓reduceIte]
    exact .trapped _ ⟨h.mem, error_below h.host _⟩
  | false =>
    have hl := hview.symm.trans hv
    have hk := ReturnBudget.read_eq h keyLen keyPtr
    have hvv := ReturnBudget.read_eq h valueLen valuePtr
    cases hkey : getMemOrReg small keyPtr keyLen with
    | none =>
      have hkeyLarge := hk.symm.trans hkey
      simp only [storageWriteFn, disallowInView, hv, hl, Bool.false_eq_true, ↓reduceIte,
        args, hkey, hkeyLarge]
      exact .trapped _ h
    | some key =>
      have hkeyLarge := hk.symm.trans hkey
      cases hvalue : getMemOrReg small valuePtr valueLen with
      | none =>
        have hvalueLarge := hvv.symm.trans hvalue
        simp only [storageWriteFn, disallowInView, hv, hl, Bool.false_eq_true, ↓reduceIte,
          args, hkey, hkeyLarge, hvalue, hvalueLarge]
        exact .trapped _ h
      | some value =>
        have hvalueLarge := hvv.symm.trans hvalue
        have hkLimit := congrArg (fun cfg => withinLimit cfg.maxStorageKeyLen key.length) h.host.config
        have hvLimit := congrArg (fun cfg => withinLimit cfg.maxStorageValueLen value.length) h.host.config
        cases hkl : withinLimit small.host.config.maxStorageKeyLen key.length with
        | false =>
          have hklLarge := hkLimit.symm.trans hkl
          simp only [storageWriteFn, disallowInView, hv, hl, Bool.false_eq_true, ↓reduceIte,
            args, hkey, hkeyLarge, hvalue, hvalueLarge, checkDataLimit, hkl, hklLarge]
          exact .trapped _ h
        | true =>
          cases hvl : withinLimit small.host.config.maxStorageValueLen value.length with
          | false =>
            have hklLarge := hkLimit.symm.trans hkl
            have hvlLarge := hvLimit.symm.trans hvl
            simp only [storageWriteFn, disallowInView, hv, hl, Bool.false_eq_true, ↓reduceIte,
              args, hkey, hkeyLarge, hvalue, hvalueLarge, checkDataLimit, hkl, hklLarge, hvl, hvlLarge]
            exact .trapped _ h
          | true =>
            change ResultBelow (storageWriteFn.invoke small [Value.i64 keyLen, Value.i64 keyPtr, Value.i64 valueLen, Value.i64 valuePtr, Value.i64 u64Max])
              (storageWriteFn.invoke large [Value.i64 keyLen, Value.i64 keyPtr, Value.i64 valueLen, Value.i64 valuePtr, Value.i64 u64Max])
            rw [storageWrite_discard small keyLen keyPtr valueLen valuePtr key value hv hkey hvalue hkl hvl,
              storageWrite_discard large keyLen keyPtr valueLen valuePtr key value hl hkeyLarge hvalueLarge
                (hkLimit.symm.trans hkl) (hvLimit.symm.trans hvl)]
            have hs := congrArg (fun st : NearState => (st.storage key).isSome) h.host.fields
            change (small.host.storage key).isSome = (large.host.storage key).isSome at hs
            rw [hs]
            exact .returned _ (written_below h key value)

/-- The proof-size observer is identical even if internal gas limits differ. -/
theorem proof_eq {small large : NearState} (h : HostBelow small large)
    (trie : _root_.Near.TrieOverlay.State) : recordedStorageError small trie = recordedStorageError large trie := by
  have hp := congrArg NearState.storageProofSize h.fields
  simp only [functional] at hp
  simp only [recordedStorageError, hp, h.config]

/-- The exact same trie receives the exact same contract key. -/
theorem reference_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (key : List UInt8) :
    small.host.storageAccounting.map (fun trie => _root_.Near.TrieOverlay.getReference trie
      (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) true) =
    large.host.storageAccounting.map (fun trie => _root_.Near.TrieOverlay.getReference trie
      (_root_.Near.TrieOverlay.contractKey large.host.context.currentAccountId key) true) := by
  have ht := congrArg NearState.storageAccounting h.host.fields
  simp only [functional] at ht
  rw [ht, h.host.context]

private theorem accounted_below {small large : HostStore NearState} (h : StoreBelow small large)
    (trie : _root_.Near.TrieOverlay.State) : StoreBelow (accounted small trie) (accounted large trie) := by
  have hf := congrArg (fun st : NearState => {st with storageAccounting := some trie}) h.host.fields
  exact ⟨h.mem, by simpa only [functional, accounted] using hf, h.host.gas⟩

private theorem prepared_below {small large : HostStore NearState} (h : StoreBelow small large)
    {lowPaid highPaid : NearState} (hp : HostBelow lowPaid highPaid)
    (trie : _root_.Near.TrieOverlay.State) :
    StoreBelow (prepared small lowPaid trie) (prepared large highPaid trie) := by
  have hf := congrArg (fun st : NearState => {st with storageAccounting := some trie}) h.host.fields
  refine ⟨h.mem, ?_, ?_⟩
  · simpa only [functional, prepared] using hf
  · exact ⟨hp.gas.burnt, h.host.gas.promises, h.host.gas.prepaid, h.host.gas.limit⟩

/-- A successful fresh-key trie phase replays at larger internal limits.
Lookup is executed on the same initial trie and contract key; the shared final
proof check is transferred from the functional state, not assumed twice. -/
theorem prepare_fresh_below {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (initial looked : _root_.Near.TrieOverlay.State)
    (haccounting : small.host.storageAccounting = some initial)
    (hkey : getMemOrReg small keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, small.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) true = .ok (looked, none))
    (hstorage : small.host.storage key = none)
    (hok : (applyCharges (accounted small looked).host (trieCharges initial looked)).2 = none)
    (hvalue : getMemOrReg small valuePtr valueLen = some value)
    (hproof : recordedStorageError small.host
      (looked.set (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) value) = none) :
    (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr)).2 = none ∧
    (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)).2 = none ∧
    StoreBelow (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr)).1
      (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)).1 := by
  have ht := congrArg NearState.storageAccounting h.host.fields
  have hcell := congrArg (fun st : NearState => st.storage key) h.host.fields
  change small.host.storageAccounting = large.host.storageAccounting at ht
  change small.host.storage key = large.host.storage key at hcell
  have hc := applyCharges_below (accounted_below h looked).host (trieCharges initial looked)
    (trieCharges_burnsOnly initial looked) hok
  have hsmall := prepare_fresh small keyLen keyPtr valueLen valuePtr key value initial looked _
    haccounting hkey hkeyLimit hlookup hstorage (Prod.ext rfl hok) hvalue
    (by rw [recordedStorageError_charges _ _ _ (trieCharges_burnsOnly initial looked)]; exact hproof)
  have hlarge := prepare_fresh large keyLen keyPtr valueLen valuePtr key value initial looked _
    (ht.symm.trans haccounting) ((ReturnBudget.read_eq h keyLen keyPtr).symm.trans hkey)
    (by rw [← h.host.config]; exact hkeyLimit)
    (by rw [← h.host.context]; exact hlookup) (hcell.symm.trans hstorage) (Prod.ext rfl hc.1)
    ((ReturnBudget.read_eq h valueLen valuePtr).symm.trans hvalue)
    (by rw [recordedStorageError_charges _ _ _ (trieCharges_burnsOnly initial looked), ← h.host.context,
      ]; change recordedStorageError large.host _ = none
        rw [← proof_eq h.host]; exact hproof)
  rw [hsmall, hlarge]
  exact ⟨rfl, rfl, by rw [← h.host.context]; exact prepared_below h hc.2 _⟩

/-- Replacement phases replay both ordered payments and the same deterministic
lookup/dereference. No large-budget trie or proof premise is required. -/
theorem prepare_replace_below {small large : HostStore NearState} (h : StoreBelow small large)
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
    (hvalueCost : (applyCharges (accounted small looked).host (evictedCharges pointer)).2 = none)
    (hnodeCost : (applyCharges
      { (applyCharges (accounted small looked).host (evictedCharges pointer)).1 with storageAccounting := some fetched }
      (trieCharges initial fetched)).2 = none)
    (hvalue : getMemOrReg small valuePtr valueLen = some value)
    (hproof : recordedStorageError small.host
      (fetched.set (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) value) = none) :
    (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr)).2 = none ∧
    (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)).2 = none ∧
    StoreBelow (prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr)).1
      (prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr)).1 := by
  have ht := congrArg NearState.storageAccounting h.host.fields
  have hcell := congrArg (fun st : NearState => st.storage key) h.host.fields
  change small.host.storageAccounting = large.host.storageAccounting at ht
  change small.host.storage key = large.host.storage key at hcell
  let lowValue := (applyCharges (accounted small looked).host (evictedCharges pointer)).1
  let highValue := (applyCharges (accounted large looked).host (evictedCharges pointer)).1
  have hfirst := applyCharges_below (accounted_below h looked).host (evictedCharges pointer)
    (evictedCharges_burnsOnly pointer) hvalueCost
  have hmid : StoreBelow (accounted {small with host := lowValue} fetched)
      (accounted {large with host := highValue} fetched) :=
    accounted_below (small := {small with host := lowValue}) (large := {large with host := highValue})
      ⟨h.mem, hfirst.2⟩ fetched
  have hsecond := applyCharges_below hmid.host (trieCharges initial fetched)
    (trieCharges_burnsOnly initial fetched) hnodeCost
  have hlowProof : recordedStorageError
      (applyCharges {lowValue with storageAccounting := some fetched} (trieCharges initial fetched)).1
      (fetched.set (_root_.Near.TrieOverlay.contractKey small.host.context.currentAccountId key) value) = none := by
    change recordedStorageError (applyCharges (accounted {small with host := lowValue} fetched).host
      (trieCharges initial fetched)).1 _ = none
    rw [recordedStorageError_charges (accounted {small with host := lowValue} fetched) _ _
      (trieCharges_burnsOnly initial fetched)]
    change recordedStorageError lowValue _ = none
    rw [recordedStorageError_charges (accounted small looked) _ _ (evictedCharges_burnsOnly pointer)]
    exact hproof
  have hhighProof : recordedStorageError
      (applyCharges {highValue with storageAccounting := some fetched} (trieCharges initial fetched)).1
      (fetched.set (_root_.Near.TrieOverlay.contractKey large.host.context.currentAccountId key) value) = none := by
    change recordedStorageError (applyCharges (accounted {large with host := highValue} fetched).host
      (trieCharges initial fetched)).1 _ = none
    rw [← h.host.context, ← proof_eq hsecond.2]
    exact hlowProof
  have hsmall := prepare_replace small keyLen keyPtr valueLen valuePtr key value old initial looked fetched pointer
    lowValue _ haccounting hkey hkeyLimit hlookup hstorage (Prod.ext rfl hvalueCost) hfetch
    (Prod.ext rfl hnodeCost) hvalue hlowProof
  have hlarge := prepare_replace large keyLen keyPtr valueLen valuePtr key value old initial looked fetched pointer
    highValue _ (ht.symm.trans haccounting) ((ReturnBudget.read_eq h keyLen keyPtr).symm.trans hkey)
    (by rw [← h.host.config]; exact hkeyLimit)
    (by rw [← h.host.context]; exact hlookup) (hcell.symm.trans hstorage) (Prod.ext rfl hfirst.1) hfetch
    (Prod.ext rfl hsecond.1) ((ReturnBudget.read_eq h valueLen valuePtr).symm.trans hvalue) hhighProof
  rw [hsmall, hlarge]
  exact ⟨rfl, rfl, by rw [← h.host.context]; exact prepared_below h hsecond.2 _⟩

local macro "unfold_storage_aux" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearVM.Metered 0) "Wasm") "Near") "prepareStorageCallAux"
  `(tactic| unfold $(Lean.mkIdent name))

/-- No trie observer is invented by the storage phase. With no accounting trie
installed, the actual phase passes through unchanged at both budgets. -/
theorem prepare_without_trie {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64) (htrie : small.host.storageAccounting = none) :
    prepareStorageCall "storage_write" small (args keyLen keyPtr valueLen valuePtr) = (small, none) ∧
    prepareStorageCall "storage_write" large (args keyLen keyPtr valueLen valuePtr) = (large, none) := by
  have ht := congrArg NearState.storageAccounting h.host.fields
  change small.host.storageAccounting = large.host.storageAccounting at ht
  have hl := ht.symm.trans htrie
  have pass (st : HostStore NearState) (ht : st.host.storageAccounting = none) :
      prepareStorageCall "storage_write" st (args keyLen keyPtr valueLen valuePtr) = (st, none) := by
    unfold prepareStorageCall
    unfold_storage_aux
    simp only [show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_write" = true by decide,
      ↓reduceIte, ht, Id.run, pure, Option.isNone_none]
    change ({st with host := {st.host with storageAccounting := none}}, none) = (st, none)
    rw [← ht]
  exact ⟨pass small htrie, pass large hl⟩

/-- Before `invokeStorageCall` interprets a phase error, the actual public
phase retains logs and the previous issue even on a failed payment or proof. -/
theorem prepare_frame (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) :
    (prepareStorageCall "storage_write" st (args keyLen keyPtr valueLen valuePtr)).1.host.logs = st.host.logs ∧
    (prepareStorageCall "storage_write" st (args keyLen keyPtr valueLen valuePtr)).1.host.lastExecutionIssue =
      st.host.lastExecutionIssue := ⟨rfl, rfl⟩

/-- The raw discard-output host cannot log or introduce a structured issue.
An external trie issue is instead installed by `invokeStorageCall` on its
terminal trap branch, and is deliberately not asserted fresh here. -/
theorem raw_frame (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) :
    (resultStore (storageWriteFn.invoke st (args keyLen keyPtr valueLen valuePtr))).host.logs = st.host.logs ∧
    (resultStore (storageWriteFn.invoke st (args keyLen keyPtr valueLen valuePtr))).host.lastExecutionIssue =
      st.host.lastExecutionIssue := by
  dsimp only [args, storageWriteFn, disallowInView, checkDataLimit, checkedSetRegister?]
  repeat' first | exact ⟨rfl, rfl⟩ | split

private theorem readSpan_burnsOnly (st : HostStore NearState) (len ptr : UInt64) :
    ∀ c ∈ readSpan st len ptr, BurnsOnly c := by
  unfold readSpan
  split
  · split <;> simp [BurnsOnly]
  · simp [BurnsOnly]

private theorem storageValue_burnsOnly (st : HostStore NearState) (key : List UInt8) :
    ∀ c ∈ storageValueCharges st "storage_write_evicted_byte" key, BurnsOnly c := by
  unfold storageValueCharges
  split
  · split <;> simp [BurnsOnly]
  · simp [BurnsOnly]

/-- Every actual pre-call storage-write charge is a burn, including invalid
argument plans and both register-sentinel span reads. -/
theorem plan_burnsOnly (st : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) :
    ∀ c ∈ chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr), BurnsOnly c := by
  obtain ⟨plan, hp⟩ := plan_exists st keyLen keyPtr valueLen valuePtr
  simp only [chargesBefore, hp]
  simp only [storageMutationPlan?, args, argU64, List.getElem?_cons_zero,
    List.getElem?_cons_succ, show ("storage_write" != "storage_write" && "storage_write" != "storage_remove") = false by decide,
    show ("storage_write" == "storage_write") = true by decide, Bool.false_eq_true, ↓reduceIte] at hp
  repeat' first
    | (cases hp; simp only [List.forall_mem_append]; simp [BurnsOnly])
    | split at hp
  all_goals repeat' first
    | exact readSpan_burnsOnly _ _ _
    | exact storageValue_burnsOnly _ _
    | constructor

/-- Successful pre-call payment replays the actual span-sensitive plan and
synchronizes the same guest-visible used gas. -/
theorem precharge_below {small large : HostStore NearState} (h : StoreBelow small large)
    (keyLen keyPtr valueLen valuePtr : UInt64)
    (hok : (applyCharges small.host
      (chargesBefore "storage_write" small (args keyLen keyPtr valueLen valuePtr))).2 = none) :
    (applyCharges large.host
      (chargesBefore "storage_write" large (args keyLen keyPtr valueLen valuePtr))).2 = none ∧
    StoreBelow (Output.paidStore small (applyCharges small.host
      (chargesBefore "storage_write" small (args keyLen keyPtr valueLen valuePtr))).1)
      (Output.paidStore large (applyCharges large.host
        (chargesBefore "storage_write" large (args keyLen keyPtr valueLen valuePtr))).1) := by
  rw [← plan_eq h keyLen keyPtr valueLen valuePtr]
  have hc := applyCharges_below h.host _ (plan_burnsOnly small keyLen keyPtr valueLen valuePtr) hok
  exact ⟨hc.1, h.mem, hc.2.syncUsed⟩

/-- The actual non-view wrapper stops at its first failed precharge with a
protocol gas error, retaining logs and the previous structured issue. Freshness
is stated explicitly so machine-level `trapError` can classify this exit. -/
theorem metered_precharge_failure (extra : Nat) (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (error : HostError)
    (hview : st.host.context.isView = false)
    (herr : (applyCharges st.host
      (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr))).2 = some error)
    (hissue : st.host.lastExecutionIssue = none) :
    let paid := Output.paidStore st (applyCharges st.host
      (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr))).1
    (metered extra "storage_write" storageWriteFn).invoke st (args keyLen keyPtr valueLen valuePtr) =
      trapWith paid error ∧
    (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧
    paid.host.logs = st.host.logs ∧ paid.host.lastExecutionIssue = none := by
  have hburn := plan_burnsOnly st keyLen keyPtr valueLen valuePtr
  have hf := applyCharges_frame st.host _ hburn
  have hl := congrArg NearState.logs hf
  have hi := congrArg NearState.lastExecutionIssue hf
  refine ⟨?_, applyCharges_error_is_gas st.host _ hburn herr, hl, hi.trans hissue⟩
  simp only [metered, show deprecatedRuntimeHost "storage_write" = false by decide,
    hview, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases hc : applyCharges st.host (chargesBefore "storage_write" st (args keyLen keyPtr valueLen valuePtr)) with
  | mk paid err =>
    have he : err = some error := by simpa only [hc] using herr
    subst err
    rfl

/-- Post-call billing depends only on the original cell; the runtime charges
its evicted-register plan even with the discard sentinel. -/
theorem afterPlan_eq {small large smallAfter largeAfter : HostStore NearState}
    (h : StoreBelow small large) (keyLen keyPtr valueLen valuePtr : UInt64) :
    chargesAfter "storage_write" small smallAfter (args keyLen keyPtr valueLen valuePtr) =
      chargesAfter "storage_write" large largeAfter (args keyLen keyPtr valueLen valuePtr) := by
  have hs := congrArg NearState.storage h.host.fields
  change small.host.storage = large.host.storage at hs
  simp only [chargesAfter, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    ReturnBudget.read_eq h keyLen keyPtr, hs]

theorem afterPlan_burnsOnly (before after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    ∀ c ∈ chargesAfter "storage_write" before after (args keyLen keyPtr valueLen valuePtr), BurnsOnly c := by
  simp only [chargesAfter, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ]
  split
  · split <;> simp [writeReg, BurnsOnly]
  · simp

private def normalized (st : HostStore NearState) : HostStore NearState :=
  {st with host := functional st.host}

private theorem normalized_eq {small large : HostStore NearState} (h : StoreBelow small large) :
    normalized small = normalized large :=
  congrArg₂ (fun mem host => (⟨mem, host⟩ : HostStore NearState)) h.mem h.host.fields

private theorem usage_normalized (extra : Nat) (before after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    functional (updateStorageUsage extra "storage_write" before after
      (args keyLen keyPtr valueLen valuePtr)).host =
      (updateStorageUsage extra "storage_write" (normalized before) (normalized after)
        (args keyLen keyPtr valueLen valuePtr)).host := by
  simp only [updateStorageUsage, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [show getMemOrReg (normalized before) keyPtr keyLen = getMemOrReg before keyPtr keyLen from rfl]
  split <;> rfl

/-- Usage and the concrete storage log update preserve the budget relation.
The full guest context is retained in the relation, including ABI wrapping. -/
theorem usage_below {small large smallAfter largeAfter : HostStore NearState}
    (h : StoreBelow small large) (ha : StoreBelow smallAfter largeAfter) (extra : Nat)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    StoreBelow (updateStorageUsage extra "storage_write" small smallAfter
      (args keyLen keyPtr valueLen valuePtr))
      (updateStorageUsage extra "storage_write" large largeAfter (args keyLen keyPtr valueLen valuePtr)) := by
  have hf := congrArg₂ (fun before after : HostStore NearState =>
      (updateStorageUsage extra "storage_write" before after (args keyLen keyPtr valueLen valuePtr)).host)
    (normalized_eq h) (normalized_eq ha)
  constructor
  · have hm (before after : HostStore NearState) :
        (updateStorageUsage extra "storage_write" before after
          (args keyLen keyPtr valueLen valuePtr)).mem = after.mem := by
      simp only [updateStorageUsage, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ]
      split <;> rfl
    rw [hm, hm]
    exact ha.mem
  · constructor
    · simpa only [usage_normalized] using hf
    · have hg (before after : HostStore NearState) :
          (updateStorageUsage extra "storage_write" before after
            (args keyLen keyPtr valueLen valuePtr)).host.gas = after.host.gas := by
        simp only [updateStorageUsage, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ]
        split <;> rfl
      rw [hg, hg]
      exact ha.host.gas

private theorem usage_frame (extra : Nat) (before after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    (updateStorageUsage extra "storage_write" before after (args keyLen keyPtr valueLen valuePtr)).host.logs =
      after.host.logs ∧
    (updateStorageUsage extra "storage_write" before after (args keyLen keyPtr valueLen valuePtr)).host.lastExecutionIssue =
      after.host.lastExecutionIssue := by
  simp only [updateStorageUsage, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ]
  split <;> exact ⟨rfl, rfl⟩

/-- Exact actual post-call operational equation; storage writes have no
promise deposit or method-encoding phase. -/
theorem finish_eq (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (result : HostResult NearState) :
    finishMeteredCall extra "storage_write" before (args keyLen keyPtr valueLen valuePtr) result =
      match result with
      | .Trap after message => .Trap after message
      | .Return values after =>
        let charged := applyCharges after.host
          (chargesAfter "storage_write" before after (args keyLen keyPtr valueLen valuePtr))
        match charged.2 with
        | some error => trapWith {after with host := charged.1} error
        | none => .Return values (updateStorageUsage extra "storage_write" before
            {after with host := charged.1} (args keyLen keyPtr valueLen valuePtr)) := by
  cases result with
  | Trap after message => rfl
  | Return values after =>
    simp only [finishMeteredCall]
    cases hc : applyCharges after.host
      (chargesAfter "storage_write" before after (args keyLen keyPtr valueLen valuePtr)) with
    | mk paid error =>
      cases error with
      | some error => rfl
      | none =>
        simp [deductDeposit, promiseDeposit?, actionMethodEncodingError, actionMethodBytes?,
          usesKeyMethodFields, functionCallInputs?]

/-- All actual post-call exits retain the functional host's logs and previous
structured issue. Gas failures only record the protocol `lastError`. -/
theorem finish_frame (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (result : HostResult NearState) :
    (resultStore (finishMeteredCall extra "storage_write" before
      (args keyLen keyPtr valueLen valuePtr) result)).host.logs = (resultStore result).host.logs ∧
    (resultStore (finishMeteredCall extra "storage_write" before
      (args keyLen keyPtr valueLen valuePtr) result)).host.lastExecutionIssue =
      (resultStore result).host.lastExecutionIssue := by
  rw [finish_eq]
  cases result with
  | Trap after message => exact ⟨rfl, rfl⟩
  | Return values after =>
    dsimp only
    have hf := applyCharges_frame after.host
      (chargesAfter "storage_write" before after (args keyLen keyPtr valueLen valuePtr))
      (afterPlan_burnsOnly before after keyLen keyPtr valueLen valuePtr)
    have hlogs := congrArg NearState.logs hf
    have hissue := congrArg NearState.lastExecutionIssue hf
    cases hc : applyCharges after.host
      (chargesAfter "storage_write" before after (args keyLen keyPtr valueLen valuePtr)) with
    | mk paid error =>
      rw [hc] at hlogs hissue
      cases error with
      | some error => exact ⟨hlogs, hissue⟩
      | none =>
        have hu := usage_frame extra before {after with host := paid} keyLen keyPtr valueLen valuePtr
        exact ⟨hu.1.trans hlogs, hu.2.trans hissue⟩

private theorem finish_replay (extra : Nat) {small large : HostStore NearState}
    (h : StoreBelow small large) (keyLen keyPtr valueLen valuePtr : UInt64)
    {smallResult largeResult : HostResult NearState} (hr : ResultBelow smallResult largeResult)
    (hissue : (resultStore smallResult).host.lastExecutionIssue = none) :
    ResultBelow
      (finishMeteredCall extra "storage_write" small (args keyLen keyPtr valueLen valuePtr) smallResult)
      (finishMeteredCall extra "storage_write" large (args keyLen keyPtr valueLen valuePtr) largeResult) ∨
    ∃ error after, (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧
      finishMeteredCall extra "storage_write" small (args keyLen keyPtr valueLen valuePtr) smallResult =
        trapWith after error ∧ after.host.lastExecutionIssue = none ∧
      after.host.logs = (resultStore (finishMeteredCall extra "storage_write" large
        (args keyLen keyPtr valueLen valuePtr) largeResult)).host.logs := by
  cases hr with
  | trapped message ha => exact Or.inl (.trapped message ha)
  | @returned smallAfter largeAfter values ha =>
    have hburn := afterPlan_burnsOnly small smallAfter keyLen keyPtr valueLen valuePtr
    have hf := applyCharges_frame smallAfter.host
      (chargesAfter "storage_write" small smallAfter (args keyLen keyPtr valueLen valuePtr)) hburn
    cases he : (applyCharges smallAfter.host
      (chargesAfter "storage_write" small smallAfter (args keyLen keyPtr valueLen valuePtr))).2 with
    | some error =>
      right
      refine ⟨error, {smallAfter with host := (applyCharges smallAfter.host
        (chargesAfter "storage_write" small smallAfter (args keyLen keyPtr valueLen valuePtr))).1},
        applyCharges_error_is_gas smallAfter.host _ hburn he, ?_, ?_, ?_⟩
      · rw [finish_eq]
        simp only [he]
      · exact (congrArg NearState.lastExecutionIssue hf).trans hissue
      · exact (congrArg NearState.logs hf).trans
          (ha.host.logs.trans (finish_frame extra large keyLen keyPtr valueLen valuePtr (.Return values largeAfter)).1.symm)
    | none =>
      have hc := applyCharges_below ha.host _ hburn he
      have hhigh : (applyCharges largeAfter.host
          (chargesAfter "storage_write" large largeAfter (args keyLen keyPtr valueLen valuePtr))).2 = none := by
        rw [← afterPlan_eq (smallAfter := smallAfter) (largeAfter := largeAfter) h keyLen keyPtr valueLen valuePtr]
        exact hc.1
      left
      rw [finish_eq, finish_eq]
      simp only [he, hhigh]
      apply ResultBelow.returned
      apply usage_below h
      rw [← afterPlan_eq (smallAfter := smallAfter) (largeAfter := largeAfter) h keyLen keyPtr valueLen valuePtr]
      exact ⟨ha.mem, hc.2⟩

/-- Complete post-call replay of the actual discard-output storage host,
including every functional trap, successful usage/log update, and low-budget
post-payment failure. This can be applied directly to the related stores
returned by either concrete successful trie-phase theorem above. -/
theorem raw_finish_replay (extra : Nat) {small large : HostStore NearState}
    (h : StoreBelow small large) (keyLen keyPtr valueLen valuePtr : UInt64)
    (hissue : small.host.lastExecutionIssue = none) :
    ResultBelow
      (finishMeteredCall extra "storage_write" small (args keyLen keyPtr valueLen valuePtr)
        (storageWriteFn.invoke small (args keyLen keyPtr valueLen valuePtr)))
      (finishMeteredCall extra "storage_write" large (args keyLen keyPtr valueLen valuePtr)
        (storageWriteFn.invoke large (args keyLen keyPtr valueLen valuePtr))) ∨
    ∃ error after, (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧
      finishMeteredCall extra "storage_write" small (args keyLen keyPtr valueLen valuePtr)
        (storageWriteFn.invoke small (args keyLen keyPtr valueLen valuePtr)) = trapWith after error ∧
      after.host.lastExecutionIssue = none ∧ after.host.logs =
        (resultStore (finishMeteredCall extra "storage_write" large (args keyLen keyPtr valueLen valuePtr)
          (storageWriteFn.invoke large (args keyLen keyPtr valueLen valuePtr)))).host.logs := by
  exact finish_replay extra h keyLen keyPtr valueLen valuePtr (raw_below h keyLen keyPtr valueLen valuePtr)
    ((raw_frame small keyLen keyPtr valueLen valuePtr).2.trans hissue)

/-- The successful raw/finish composition preserves freshness, while retaining
logs on every exit including its low-gas trap. -/
theorem raw_finish_frame (extra : Nat) (st : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    (resultStore (finishMeteredCall extra "storage_write" st (args keyLen keyPtr valueLen valuePtr)
      (storageWriteFn.invoke st (args keyLen keyPtr valueLen valuePtr)))).host.logs = st.host.logs ∧
    (resultStore (finishMeteredCall extra "storage_write" st (args keyLen keyPtr valueLen valuePtr)
      (storageWriteFn.invoke st (args keyLen keyPtr valueLen valuePtr)))).host.lastExecutionIssue = st.host.lastExecutionIssue := by
  have hf := finish_frame extra st keyLen keyPtr valueLen valuePtr
    (storageWriteFn.invoke st (args keyLen keyPtr valueLen valuePtr))
  have hr := raw_frame st keyLen keyPtr valueLen valuePtr
  exact ⟨hf.1.trans hr.1, hf.2.trans hr.2⟩

end Wasm.Near.MeteredHosts.StorageBudget
