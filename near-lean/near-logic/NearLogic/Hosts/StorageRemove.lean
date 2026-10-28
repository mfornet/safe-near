import NearLogic.Hosts.StorageHasKey

/-!
# `storage_remove`, metered

The host contract of metered `storage_remove(key_len, key_ptr, register_id)` with the key in
memory, over a host whose storage accounting is a canonical overlay linked to its `storage`
(`viewVal`), as `storage_write` (`StorageWrite.lean`).

* `prepareStorageCallAux_remove`: the storage phase for a mutation succeeds. It looks the raw key
  up with `accountNodes = true` (`storage_lookup_view`), bills the old value's bytes
  (`storage_remove_ret_value_byte`), dereferences it, stages the removal (`State.remove`, before
  the final charge), bills the trie nodes (at most `2·|rawKey| + 2` at the dearer node cost), and
  the recorded-proof check after it passes: the operations (`ProofReach`: lookup, dereference,
  remove) record at most `removeProofCost`, within the budget. A removal records
  `removalProofCharge` even when the key is absent.
* `storageRemove_ok`: the whole metered call: returns `storageReadResult` of the old value, the
  old value in register `r` (`storageReadRegs`), the key removed, the usage updated
  (`removeUsage`, as `updateStorageUsage`) and the removal logged: `storageRemoveHost`, up to gas
  and with the accounting `s1.remove rawKey` for some `s1` with the data of `s`
  (`StorageRemovePost`). The gas is at most `storageRemoveUse`.
* `storageRemove_readContract`: the call as a `ReadContractP`.
* `StorageRemovePost.next`: what the removal leaves meets the next storage call's hypotheses.

The call must not be a view call: `storage_remove` is prohibited in views.
-/

namespace NearLogic

open Wasm Wasm.Near Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-- The gas the storage phase of `storage_remove` may burn, for the raw trie key `rawKey` and the
old value `old`: the old value's bytes, then the nodes of the lookup and the dereference. -/
def storageRemovePhaseUse (h : NearState) (rawKey : List UInt8) (old : Option (List UInt8)) : Nat :=
  (2 * rawKey.length + 2) * trieNodeMax h +
    ((old.map fun v => chargesUse h [.ext "storage_remove_ret_value_byte" v.length]).getD 0)

/-- The most a `storage_remove` of `rawKey` over the old value `old` records: the lookup, the
dereference and the removal. -/
def removeProofCost (rawKey : List UInt8) (old : Option (List UInt8)) : Nat :=
  writeProofCost rawKey old + removalProofCharge

@[simp] theorem State.remove_accounting (s : State) (k : List UInt8) :
    (s.remove k).accounting = s.accounting := rfl

theorem prepareStorageCallAux_remove (before : HostStore NearState) (kl kp r : UInt64)
    (key rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before kp kl = some key)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : removeProofCost rawKey (before.host.storage key) ≤ b)
    (h1 : before.host.gas.used + storageRemovePhaseUse before.host rawKey (before.host.storage key) ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ after s1, prepareStorageCallAux "storage_remove" before [.i64 kl, .i64 kp, .i64 r] =
        (after, none) ∧
      after.host.storageAccounting = some (s1.remove rawKey) ∧ SameData s s1 ∧
      ProofReach s (s1.remove rawKey) (removeProofCost rawKey (before.host.storage key)) ∧
      after.host.gas.burnt ≤
        before.host.gas.burnt + storageRemovePhaseUse before.host rawKey (before.host.storage key) ∧
      after.host.gas.promises = before.host.gas.promises := by
  obtain ⟨s', p, hget, hsd, ⟨d, m, hd, hm, hdm⟩, hpres, hder⟩ :=
    storage_lookup_view (k := rawKey) true hb hz
  have hcon : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "storage_remove" = true := by decide
  have e1 : ("storage_remove" == "storage_write") = false := by decide
  have e2 : ("storage_remove" == "storage_remove") = true := by decide
  have e3 : ("storage_remove" != "storage_has_key") = true := by decide
  have e4 : ("storage_remove" == "storage_read") = false := by decide
  have hlk : ∀ l, before.host.config.maxStorageKeyLen = some l → ¬ key.length > l := by
    intro l hl; rw [hl] at hlim; simpa [withinLimit] using hlim
  rw [← hlink] at hpres hder
  have hpres' : (p.isSome != (before.host.storage key).isSome) = false := by
    rw [hpres]; exact bne_self_eq_false _
  have hfb : (2 * rawKey.length + 2) * trieNodeMax before.host ≤
      storageRemovePhaseUse before.host rawKey (before.host.storage key) := by
    unfold storageRemovePhaseUse; omega
  simp only [prepareStorageCallAux, hcon, hacc, argU64, Id.run]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, hkey, e1, e2, e3, e4,
    Bool.or_false, Bool.true_or, Bool.or_true, ite_true, Bool.false_eq_true, ite_false]
  rw [← hraw, hget]
  split
  on_goal 1 => rename_i lim hml; rw [if_neg (hlk lim hml)]
  all_goals
    dsimp only
    rw [hpres']
    simp only [Bool.false_eq_true, ite_false]
    rcases hv : before.host.storage key with _ | v
    · ------------------------------------------------------------ no old value
      have hpn : p = none := by
        cases p with
        | none => rfl
        | some _ => rw [hv] at hpres; cases hpres
      subst hpn
      dsimp only
      have hdd : s'.accounting.disk - s.accounting.disk = d := by omega
      have hmm : s'.accounting.mem - s.accounting.mem = m := by omega
      simp only [State.remove_accounting, hdd, hmm]
      set ns0 : NearState := { before.host with storageAccounting := some (s'.remove rawKey) } with hns0
      have hu0 : ns0.gas = before.host.gas := rfl
      have htc : chargesUse ns0 (trieNodeCharges d m) ≤ (2 * rawKey.length + 2) * trieNodeMax before.host :=
        Nat.le_trans (trieNodeCharges_use ns0 d m) (Nat.mul_le_mul_right _ (by omega))
      rw [hv] at hfb h1
      obtain ⟨ns1, hA, ch1, pr1⟩ := bill_ext ns0 (trieNodeCharges d m) (extOnly_trie d m) (C := C)
        (by rw [hu0]; omega) h2 h3
      simp only [trieNodeCharges] at hA
      rw [hA]
      have hreach : ProofReach s (s'.remove rawKey) (removeProofCost rawKey none) := by
        have := ProofReach.step (ProofStep.lookup hget) (ProofReach.step (ProofStep.remove s' rawKey)
          (ProofReach.refl _))
        simpa [removeProofCost, writeProofCost] using this
      have hpsz : ns1.storageProofSize = before.host.storageProofSize :=
        erase_field ch1.erase NearState.storageProofSize fun _ => rfl
      have hrec : recordedStorageError ns1 (s'.remove rawKey) = none :=
        recordedStorageError_reach (hproof.congr hpsz ch1.config) hreach (by rw [hv] at hbud; exact hbud)
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hrec]
      have hsa1 : ns1.storageAccounting = some (s'.remove rawKey) :=
        erase_field ch1.erase NearState.storageAccounting fun _ => rfl
      refine ⟨_, s', rfl, hsa1, hsd, hreach, ?_, pr1⟩
      have hu1 := ch1.used
      rw [hu0] at hu1
      have q1 := pr1
      rw [hu0] at q1
      simp only [Near.GasCounter.used] at hu1 h1
      show ns1.gas.burnt ≤ _
      omega
    · ------------------------------------------------------------ an old value
      obtain ⟨q, s'', rfl, hq, hd2, hsd2⟩ := hder v hv
      obtain ⟨d2, m2, hd2', hm2', hdm2⟩ := dereference_counters_le hd2
      dsimp only
      rw [hq]
      have hrl : (refOf v).length = v.length := rfl
      rw [hrl]
      rw [hv] at hfb h1 hbud
      set ns0 : NearState := { before.host with storageAccounting := some s' } with hns0
      have hu0 : ns0.gas = before.host.gas := rfl
      have hev : chargesUse ns0 [Charge.ext "storage_remove_ret_value_byte" v.length] =
          chargesUse before.host [Charge.ext "storage_remove_ret_value_byte" v.length] := rfl
      have hph : storageRemovePhaseUse before.host rawKey (some v) =
          (2 * rawKey.length + 2) * trieNodeMax before.host +
          chargesUse before.host [Charge.ext "storage_remove_ret_value_byte" v.length] := rfl
      obtain ⟨ns1, hA1, ch1, pr1⟩ := bill_ext ns0 [Charge.ext "storage_remove_ret_value_byte" v.length]
        (extOnly_one _ _) (C := C) (by rw [hu0, hev]; omega) h2 h3
      rw [hA1]
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hd2]
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, State.remove_accounting]
      set ns1' : NearState := { ns1 with storageAccounting := some (s''.remove rawKey) } with hns1'
      have hdd : s''.accounting.disk - s.accounting.disk = d + d2 := by omega
      have hmm : s''.accounting.mem - s.accounting.mem = m + m2 := by omega
      simp only [hdd, hmm]
      have hf1 : ns1'.fees = before.host.fees := ch1.fees
      have hx1 : ns1'.extCosts = before.host.extCosts := ch1.extCosts
      have htc : chargesUse ns1' (trieNodeCharges (d + d2) (m + m2)) ≤
          (2 * rawKey.length + 2) * trieNodeMax before.host := by
        have := trieNodeCharges_use ns1' (d + d2) (m + m2)
        have hmx : trieNodeMax ns1' = trieNodeMax before.host := by simp only [trieNodeMax, hx1]
        rw [hmx] at this
        exact Nat.le_trans this (Nat.mul_le_mul_right _ (by omega))
      have hu1 := ch1.used
      have hg1 : ns1'.gas = ns1.gas := rfl
      obtain ⟨ns2, hA2, ch2, pr2⟩ := bill_ext ns1' (trieNodeCharges (d + d2) (m + m2)) (extOnly_trie _ _) (C := C)
        (by rw [hg1, hu1, hu0, hev]; omega) (by rw [hg1, ch1.maxBurnt]; exact h2)
        (by rw [hg1, ch1.prepaid]; exact h3)
      simp only [trieNodeCharges] at hA2
      rw [hA2]
      have hreach : ProofReach s (s''.remove rawKey) (removeProofCost rawKey (some v)) := by
        have := ProofReach.step (ProofStep.lookup hget) (ProofReach.step (ProofStep.dereference hd2)
          (ProofReach.step (ProofStep.remove s'' rawKey) (ProofReach.refl _)))
        simp only [removeProofCost, writeProofCost, Option.map_some, Option.getD_some]
        simpa [Nat.add_assoc] using this
      have hpsz : ns2.storageProofSize = before.host.storageProofSize :=
        (erase_field ch2.erase NearState.storageProofSize fun _ => rfl).trans
          (erase_field ch1.erase NearState.storageProofSize fun _ => rfl)
      have hcf : ns2.config = before.host.config := ch2.config.trans ch1.config
      have hrec : recordedStorageError ns2 (s''.remove rawKey) = none :=
        recordedStorageError_reach (hproof.congr hpsz hcf) hreach hbud
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hrec]
      have hsa2 : ns2.storageAccounting = some (s''.remove rawKey) :=
        erase_field ch2.erase NearState.storageAccounting fun _ => rfl
      refine ⟨_, s'', rfl, hsa2, ?_, hreach, ?_, ?_⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hsd
        obtain ⟨b1, b2, b3, b4⟩ := hsd2
        exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩
      · have hu2 := ch2.used
        rw [hu0, hev] at hu1
        simp only [Near.GasCounter.used] at hu1 hu2 h1
        rw [hg1] at hu2
        have q2 := pr2
        rw [hg1] at q2
        have q1 := pr1
        rw [hu0] at q1
        show ns2.gas.burnt ≤ _
        omega
      · show ns2.gas.promises = _
        rw [pr2, hg1, pr1]

/-- The storage phase of `storage_remove`, as the metered wrapper sees it. -/
theorem prepareStorageCall_remove (before : HostStore NearState) (kl kp r : UInt64)
    (key rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before kp kl = some key)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : removeProofCost rawKey (before.host.storage key) ≤ b)
    (h1 : before.host.gas.used + storageRemovePhaseUse before.host rawKey (before.host.storage key) ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ s1 bt p, prepareStorageCall "storage_remove" before [.i64 kl, .i64 kp, .i64 r] =
        ({ before with host := phaseHost before.host (s1.remove rawKey) bt p }, none) ∧ SameData s s1 ∧
      ProofReach s (s1.remove rawKey) (removeProofCost rawKey (before.host.storage key)) ∧
      bt ≤ before.host.gas.burnt + storageRemovePhaseUse before.host rawKey (before.host.storage key) := by
  obtain ⟨after, s1, haux, hsa, hsd, hre, hb', -⟩ :=
    prepareStorageCallAux_remove before kl kp r key rawKey s hraw hacc hkey hlim hb hz hlink
      hproof hbud h1 h2 h3
  refine ⟨s1, after.host.gas.burnt, after.host.gasProfile, ?_, hsd, hre, hb'⟩
  simp only [prepareStorageCall, haux, hsa, Option.isNone_none, ite_true, phaseHost]

/-! ## The metered call -/

/-- The charges of `storage_remove` before it runs, for a key of `k` bytes in memory. -/
def storageRemoveBeforeCharges (k : Nat) : List Charge :=
  [.ext "base", .ext "storage_remove_base", .ext "read_memory_base", .ext "read_memory_byte" k,
    .ext "storage_remove_key_byte" k]

theorem storageMutationPlan_remove (st : HostStore NearState) (kl kp r : UInt64) (key : List UInt8)
    (hkl : kl ≠ u64Max) (hkey : getMemOrReg st kp kl = some key)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hacc : st.host.storageAccounting.isSome = true) :
    storageMutationPlan? "storage_remove" st [.i64 kl, .i64 kp, .i64 r] =
      some { charges := [.ext "base", .ext "storage_remove_base", .ext "read_memory_base",
        .ext "read_memory_byte" kl.toNat, .ext "storage_remove_key_byte" key.length] } := by
  have hlk : ∀ l, st.host.config.maxStorageKeyLen = some l → ¬ key.length > l := by
    intro l hl; rw [hl] at hlim; simpa [withinLimit] using hlim
  have hsv : storageValueCharges st "storage_remove_ret_value_byte" key = [] := by
    unfold storageValueCharges
    cases h : st.host.storageAccounting with
    | none => rw [h] at hacc; cases hacc
    | some _ => simp
  simp only [storageMutationPlan?, argU64, List.getElem?_cons_succ, List.getElem?_cons_zero,
    hkey, readSpan, hkl, ite_false, hsv, List.append_nil]
  simp only [show ("storage_remove" != "storage_write") = true by decide,
    show ("storage_remove" != "storage_remove") = false by decide,
    show ("storage_remove" == "storage_write") = false by decide, Bool.and_false, Bool.false_eq_true,
    ite_false]
  cases hk : st.host.config.maxStorageKeyLen with
  | none => rfl
  | some lk => simp only [hlk lk hk, ite_false]; rfl

theorem chargesBefore_storageRemove (st : HostStore NearState) (kl kp r : UInt64) (key : List UInt8)
    (hkl : kl ≠ u64Max) (hkey : getMemOrReg st kp kl = some key) (hkn : key.length = kl.toNat)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hacc : st.host.storageAccounting.isSome = true) :
    chargesBefore "storage_remove" st [.i64 kl, .i64 kp, .i64 r] = storageRemoveBeforeCharges kl.toNat := by
  unfold chargesBefore
  rw [storageMutationPlan_remove st kl kp r key hkl hkey hlim hacc, hkn]
  rfl

theorem preInvokeError_storageRemove (st : HostStore NearState) (kl kp r : UInt64) (key : List UInt8)
    (hkl : kl ≠ u64Max) (hkey : getMemOrReg st kp kl = some key)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hacc : st.host.storageAccounting.isSome = true) :
    preInvokeError "storage_remove" st [.i64 kl, .i64 kp, .i64 r] = none := by
  unfold preInvokeError invocationArgumentError
  rw [storageMutationPlan_remove st kl kp r key hkl hkey hlim hacc]
  simp [allocatesPromise, functionCallInputError, functionCallInputs?]

/-- The host function's own effect: on a hit, the old value to register `r` and the key removed,
with the iterators invalidated; on a miss, nothing. -/
def removeRegs (h : NearState) (key : List UInt8) (r : UInt64) (old : Option (List UInt8)) : NearState :=
  match old with
  | some v => ((storageReadRegs h r (some v)).removeStorage key).invalidateIterators
  | none => h

/-- `storage_remove` itself, after the metering. -/
theorem storageRemoveFn_invoke (st : HostStore NearState) (kl kp r : UInt64) (key : List UInt8)
    (hview : st.host.context.isView = false)
    (hkey : getMemOrReg st kp kl = some key)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hreg : ∀ v, st.host.storage key = some v → r ≠ u64Max →
      withinLimit st.host.config.maxRegisterLen v.length = true) :
    storageRemoveFn.invoke st [.i64 kl, .i64 kp, .i64 r] =
      .Return (storageReadResult (st.host.storage key))
        { st with host := removeRegs st.host key r (st.host.storage key) } := by
  simp only [storageRemoveFn, disallowInView, hview, Bool.false_eq_true, ite_false, hkey, checkDataLimit,
    hlim, ite_true]
  cases hv : st.host.storage key with
  | none => rfl
  | some v =>
    simp only [checkedSetRegister?, storageReadResult, removeRegs, storageReadRegs]
    by_cases hr : r = u64Max
    · simp [hr]
    · simp [hr, hreg v hv hr]

/-- The contract's storage usage after removing `key` over `old` (`updateStorageUsage`): a
removed record frees the key, the value and `extra`. -/
def removeUsage (extra : Nat) (key : List UInt8) (old : Option (List UInt8)) (usage : Nat) : Nat :=
  match old with
  | none => usage
  | some o => usage - (key.length + o.length + extra)

/-- The usage and log update of a storage removal. -/
def logRemove (extra : Nat) (old : Option (List UInt8)) (usage : Nat) (key : List UInt8) (x : NearState) :
    NearState :=
  { x with
    context := { x.context with storageUsage := UInt64.ofNat (removeUsage extra key old usage) }
    storageLog := { key, existed := old.isSome, value := none } :: x.storageLog }

theorem erase_logRemove (extra : Nat) (old : Option (List UInt8)) (usage : Nat) (key : List UInt8)
    (x : NearState) : erase (logRemove extra old usage key x) = logRemove extra old usage key (erase x) := rfl

theorem erase_removeRegs (h : NearState) (key : List UInt8) (r : UInt64) (old : Option (List UInt8)) :
    erase (removeRegs h key r old) = removeRegs (erase h) key r old := by
  unfold removeRegs; split
  · rename_i v
    rw [show ∀ x : NearState, erase ((x.removeStorage key).invalidateIterators) =
      ((erase x).removeStorage key).invalidateIterators from fun _ => rfl, erase_storageReadRegs]
  · rfl

/-- What `storage_remove(key)` into register `r` leaves of `h`, up to gas, once its accounting is
`s2`: the old value in register `r`, the key removed, the iterators invalidated (on a hit), the
storage usage updated and the removal logged. -/
def storageRemoveHost (extra : Nat) (h : NearState) (key : List UInt8) (r : UInt64) (s2 : State) : NearState :=
  logRemove extra (h.storage key) h.context.storageUsage.toNat key
    (removeRegs { h with storageAccounting := some s2 } key r (h.storage key))

/-- The charges after `storage_remove`: writing the old value to the register. -/
def storageRemoveAfter (old : Option (List UInt8)) : List Charge :=
  (old.map fun v => writeReg v.length).getD []

theorem chargesAfter_storageRemove (before st : HostStore NearState) (kl kp r : UInt64) (key : List UInt8)
    (hkey : getMemOrReg before kp kl = some key) :
    chargesAfter "storage_remove" before st [.i64 kl, .i64 kp, .i64 r] =
      storageRemoveAfter (before.host.storage key) := by
  simp only [chargesAfter, argU64, List.getElem?_cons_succ, List.getElem?_cons_zero, hkey]
  cases before.host.storage key <;> rfl

/-- Post-call metering of `storage_remove`: the after-charges, then the usage and the log. -/
theorem finish_storageRemove (extra : Nat) (before st : HostStore NearState) (kl kp r : UInt64)
    (key : List UInt8) (vals : List Value)
    (hkey : getMemOrReg before kp kl = some key) (hst : st.host.storage key = none)
    (h : (applyCharges st.host (storageRemoveAfter (before.host.storage key))).2 = none) :
    finishMeteredCall extra "storage_remove" before [.i64 kl, .i64 kp, .i64 r] (.Return vals st) =
      .Return vals { st with host := (logRemove extra (before.host.storage key)
        (applyCharges st.host (storageRemoveAfter (before.host.storage key))).1.context.storageUsage.toNat key
        (applyCharges st.host (storageRemoveAfter (before.host.storage key))).1) } := by
  simp only [finishMeteredCall]
  rw [chargesAfter_storageRemove before st kl kp r key hkey]
  have hsA : (applyCharges st.host (storageRemoveAfter (before.host.storage key))).1.storage = st.host.storage :=
    erase_field (applyCharges_erase _ _) NearState.storage fun _ => rfl
  generalize applyCharges st.host (storageRemoveAfter (before.host.storage key)) = A at h hsA ⊢
  obtain ⟨ns, e⟩ := A
  simp only at h
  subst h
  have hd : deductDeposit "storage_remove" before { st with host := ns }
      [.i64 kl, .i64 kp, .i64 r] = ({ st with host := ns }, none) := by
    simp (config := { decide := true }) [deductDeposit, promiseDeposit?]
  have ha : actionMethodEncodingError "storage_remove" before [.i64 kl, .i64 kp, .i64 r] = none := by
    simp (config := { decide := true }) [actionMethodEncodingError, actionMethodBytes?, functionCallInputs?]
  simp only [hd, ha]
  simp only at hsA
  have hns : ns.storage key = none := by rw [hsA]; exact hst
  simp only [updateStorageUsage, hns, argU64, List.getElem?_cons_succ, List.getElem?_cons_zero, hkey]
  cases before.host.storage key <;> rfl

/-- What `storage_remove(key)` into register `r` leaves, up to gas, from `h` with accounting `s`:
the host as `storageRemoveHost`, whose accounting is the removal staged on one with the data of
`s`, reached by operations recording at most `removeProofCost`. -/
def StorageRemovePost (extra : Nat) (h : NearState) (key : List UInt8) (r : UInt64) (s : State)
    (host' : NearState) : Prop :=
  ∃ s1, SameData s s1 ∧
    ProofReach s (s1.remove (contractKey h.context.currentAccountId key))
      (removeProofCost (contractKey h.context.currentAccountId key) (h.storage key)) ∧
    erase host' = erase (storageRemoveHost extra h key r (s1.remove (contractKey h.context.currentAccountId key)))

/-- The gas `storage_remove` of a `k`-byte key may use: the charges before, the storage phase
(`storageRemovePhaseUse`), and writing the old value to the register. -/
def storageRemoveUse (h : NearState) (key : List UInt8) (k : Nat) : Nat :=
  chargesUse h (storageRemoveBeforeCharges k) +
    storageRemovePhaseUse h (contractKey h.context.currentAccountId key) (h.storage key) +
    chargesUse h (storageRemoveAfter (h.storage key))

theorem removeRegs_fees (h : NearState) (key : List UInt8) (r : UInt64) (old : Option (List UInt8)) :
    (removeRegs h key r old).fees = h.fees ∧ (removeRegs h key r old).extCosts = h.extCosts := by
  unfold removeRegs; split
  · exact storageReadRegs_fees h r _
  · exact ⟨rfl, rfl⟩

@[simp] theorem removeRegs_gas (h : NearState) (key : List UInt8) (r : UInt64) (old : Option (List UInt8)) :
    (removeRegs h key r old).gas = h.gas := by
  unfold removeRegs; split
  · show (storageReadRegs h r _).gas = _
    exact storageReadRegs_gas h r _
  · rfl

theorem removeRegs_context (h : NearState) (key : List UInt8) (r : UInt64) (old : Option (List UInt8)) :
    (removeRegs h key r old).context = h.context := by
  unfold removeRegs; split
  · show (storageReadRegs h r _).context = _
    exact storageReadRegs_context h r _
  · rfl

theorem removeRegs_storage_key (h : NearState) (key : List UInt8) (r : UInt64) (old : Option (List UInt8))
    (hold : h.storage key = old) : (removeRegs h key r old).storage key = none := by
  unfold removeRegs; split
  · simp [NearState.invalidateIterators, NearState.removeStorage]
  · assumption

/-- The metered call on a store: the charges before, the storage phase, the host function and
the charges after all succeed within the credits. -/
theorem storageRemove_ok (extra : Nat) (st : HostStore NearState) (kl kp r : UInt64) (key : List UInt8)
    (s : State) {C b : Nat} (hkl : kl ≠ u64Max)
    (hview : st.host.context.isView = false)
    (hkey : getMemOrReg st kp kl = some key) (hkn : key.length = kl.toNat)
    (hacc : st.host.storageAccounting = some s)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : st.host.storage key = viewVal s (contractKey st.host.context.currentAccountId key))
    (hproof : ProofBudget st.host s b)
    (hbud : removeProofCost (contractKey st.host.context.currentAccountId key) (st.host.storage key) ≤ b)
    (hreg : ∀ v, st.host.storage key = some v → r ≠ u64Max →
      withinLimit st.host.config.maxRegisterLen v.length = true)
    (h1 : st.host.gas.used + storageRemoveUse st.host key kl.toNat ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "storage_remove" storageRemoveFn).invoke st [.i64 kl, .i64 kp, .i64 r] =
        .Return (storageReadResult (st.host.storage key)) { mem := st.mem, host := host' } ∧
      StorageRemovePost extra st.host key r s host' ∧
      host'.gas.used ≤ st.host.gas.used + storageRemoveUse st.host key kl.toNat ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  have hdep : deprecatedRuntimeHost "storage_remove" = false := by decide
  have hu := h1
  unfold storageRemoveUse at hu
  have haccs : st.host.storageAccounting.isSome = true := by rw [hacc]; rfl
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (storageRemoveBeforeCharges kl.toNat) (C := C)
    (by omega) h2 h3
  simp only [metered, hdep, hview, Bool.false_and, Bool.false_eq_true, ite_false]
  rw [chargesBefore_storageRemove st kl kp r key hkl hkey hkn hlim haccs]
  generalize hac : applyCharges st.host (storageRemoveBeforeCharges kl.toNat) = ac at hok hch
  obtain ⟨ns, err⟩ := ac
  simp only at hok hch
  subst hok
  simp only
  have he1 : erase (afterCharges ns) = erase st.host := by rw [erase_afterCharges, hch.erase]
  have fsa : (afterCharges ns).storageAccounting = st.host.storageAccounting :=
    erase_field he1 NearState.storageAccounting fun _ => rfl
  have fid : (afterCharges ns).context.currentAccountId = st.host.context.currentAccountId :=
    erase_field he1 (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have fview : (afterCharges ns).context.isView = st.host.context.isView :=
    erase_field he1 (fun x : NearState => x.context.isView) fun _ => rfl
  have fcfg : (afterCharges ns).config = st.host.config := erase_field he1 NearState.config fun _ => rfl
  have fsto : (afterCharges ns).storage = st.host.storage := erase_field he1 NearState.storage fun _ => rfl
  have fpsz : (afterCharges ns).storageProofSize = st.host.storageProofSize :=
    erase_field he1 NearState.storageProofSize fun _ => rfl
  have ffee : (afterCharges ns).fees = st.host.fees := erase_field he1 NearState.fees fun _ => rfl
  have fext : (afterCharges ns).extCosts = st.host.extCosts := erase_field he1 NearState.extCosts fun _ => rfl
  have hgas1 : (afterCharges ns).gas = ns.gas := rfl
  have hkey1 : getMemOrReg { mem := st.mem, host := afterCharges ns } kp kl = some key :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := afterCharges ns }) hkl rfl).trans hkey
  erw [preInvokeError_storageRemove { mem := st.mem, host := afterCharges ns } kl kp r key hkl
    hkey1 (by rw [fcfg]; exact hlim) (by rw [fsa]; exact haccs)]
  simp only
  show ∃ host', invokeStorageCall extra "storage_remove" storageRemoveFn
    { mem := st.mem, host := afterCharges ns } [.i64 kl, .i64 kp, .i64 r] = _ ∧ _
  have hphase : storageRemovePhaseUse (afterCharges ns) (contractKey st.host.context.currentAccountId key)
      ((afterCharges ns).storage key) =
      storageRemovePhaseUse st.host (contractKey st.host.context.currentAccountId key) (st.host.storage key) := by
    simp only [storageRemovePhaseUse, trieNodeMax, fext, fsto]
    cases st.host.storage key <;> simp [chargesUse_of ffee fext]
  obtain ⟨s1, bt, p, hpre, hsd, hre, hbb⟩ := prepareStorageCall_remove { mem := st.mem, host := afterCharges ns }
    kl kp r key (contractKey st.host.context.currentAccountId key) s (C := C) (by rw [fid])
    (by rw [fsa]; exact hacc) hkey1 (by rw [fcfg]; exact hlim) hb hz
    (by rw [fsto]; exact hlink) (hproof.congr fpsz fcfg) (by rw [fsto]; exact hbud)
    (by rw [hphase, hgas1, hch.used]; omega) (by rw [hgas1, hch.maxBurnt]; exact h2)
    (by rw [hgas1, hch.prepaid]; exact h3)
  rw [hphase] at hbb
  have hbb' : bt ≤ ns.gas.burnt + storageRemovePhaseUse st.host (contractKey st.host.context.currentAccountId key)
      (st.host.storage key) := hbb
  rw [fsto] at hre
  simp only [invokeStorageCall, hpre]
  set s2 := s1.remove (contractKey st.host.context.currentAccountId key) with hs2
  set H2 := phaseHost (afterCharges ns) s2 bt p with hH2
  have hkey2 : getMemOrReg { mem := st.mem, host := H2 } kp kl = some key :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := H2 }) hkl rfl).trans hkey
  have hsto2 : H2.storage = st.host.storage := fsto
  have hcfg2 : H2.config = st.host.config := fcfg
  have hview2 : H2.context.isView = false := by rw [← hview]; exact fview
  rw [storageRemoveFn_invoke { mem := st.mem, host := H2 } kl kp r key hview2 hkey2
    (by rw [hcfg2]; exact hlim) (by rw [hcfg2, hsto2]; exact hreg)]
  rw [hsto2]
  set H3 := removeRegs H2 key r (st.host.storage key) with hH3
  have hst3 : H3.storage key = none := removeRegs_storage_key H2 key r _ (by rw [hsto2])
  set cs := storageRemoveAfter (st.host.storage key) with hcs
  have hfe3 := removeRegs_fees H2 key r (st.host.storage key)
  have hcu : chargesUse H3 cs = chargesUse st.host cs :=
    chargesUse_of (hfe3.1.trans ffee) (hfe3.2.trans fext) cs
  have hg3 : H3.gas = { ns.gas with burnt := bt } := by
    rw [hH3, removeRegs_gas]; rfl
  have hn := hch.used
  simp only [Near.GasCounter.used] at hn hu
  obtain ⟨ok4, ch4⟩ := applyCharges_ok H3 cs (C := C)
    (by rw [hcu, hg3]; simp only [Near.GasCounter.used]; omega)
    (by rw [hg3]; show C ≤ ns.gas.maxBurnt; rw [hch.maxBurnt]; exact h2)
    (by rw [hg3]; show C ≤ ns.gas.prepaid; rw [hch.prepaid]; exact h3)
  have hfin := finish_storageRemove extra { mem := st.mem, host := H2 } { mem := st.mem, host := H3 }
    kl kp r key (storageReadResult (st.host.storage key)) hkey2 hst3 (by rw [hsto2]; exact ok4)
  simp only [hsto2] at hfin
  rw [hfin]
  have hus : (applyCharges H3 cs).1.context.storageUsage = st.host.context.storageUsage := by
    have e3 : erase (applyCharges H3 cs).1 = erase H3 := ch4.erase
    rw [erase_field e3 (fun x : NearState => x.context.storageUsage) fun _ => rfl]
    rw [hH3, removeRegs_context]
    exact erase_field he1 (fun x : NearState => x.context.storageUsage) fun _ => rfl
  refine ⟨_, rfl, ⟨s1, hsd, hre, ?_⟩, ?_, ?_, ?_⟩
  · rw [erase_logRemove, ch4.erase, hus, hH3, erase_removeRegs]
    unfold storageRemoveHost
    rw [erase_logRemove, erase_removeRegs]
    have hE : erase H2 = erase { st.host with storageAccounting := some s2 } := by
      show { erase (afterCharges ns) with storageAccounting := some s2 } = _
      rw [he1]; rfl
    rw [hE]
  · show (applyCharges H3 cs).1.gas.used ≤ _
    rw [ch4.used, hcu, hg3]
    show _ ≤ st.host.gas.used + (_ + _ + chargesUse st.host cs)
    simp only [Near.GasCounter.used]
    omega
  · show (applyCharges H3 cs).1.gas.maxBurnt = _
    rw [ch4.maxBurnt, hg3]; exact hch.maxBurnt
  · show (applyCharges H3 cs).1.gas.prepaid = _
    rw [ch4.prepaid, hg3]; exact hch.prepaid

theorem storageRemoveUse_erase {h h' : NearState} (he : erase h = erase h') (key : List UInt8) (k : Nat) :
    storageRemoveUse h key k = storageRemoveUse h' key k := by
  have hf : h.fees = h'.fees := erase_field he NearState.fees fun _ => rfl
  have hx : h.extCosts = h'.extCosts := erase_field he NearState.extCosts fun _ => rfl
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  have hi : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  unfold storageRemoveUse storageRemovePhaseUse trieNodeMax
  rw [hs, hi, hx, chargesUse_of hf hx, chargesUse_of hf hx]
  cases h'.storage key <;> simp [chargesUse_of hf hx]

theorem storageRemoveHost_erase {h h' : NearState} (he : erase h = erase h') (extra : Nat) (key : List UInt8)
    (r : UInt64) (s2 : State) :
    erase (storageRemoveHost extra h key r s2) = erase (storageRemoveHost extra h' key r s2) := by
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  have hu : h.context.storageUsage = h'.context.storageUsage :=
    erase_field he (fun x : NearState => x.context.storageUsage) fun _ => rfl
  have hw : erase { h with storageAccounting := some s2 } = erase { h' with storageAccounting := some s2 } := by
    show { erase h with storageAccounting := some s2 } = { erase h' with storageAccounting := some s2 }
    rw [he]
  unfold storageRemoveHost
  rw [erase_logRemove, erase_logRemove, erase_removeRegs, erase_removeRegs, hw, hs, hu]

theorem storageRemovePost_erase {h h' host' : NearState} (he : erase h = erase h') {extra : Nat}
    {key : List UInt8} {r : UInt64} {s : State} (hq : StorageRemovePost extra h key r s host') :
    StorageRemovePost extra h' key r s host' := by
  obtain ⟨s1, hsd, hre, hq⟩ := hq
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  have hi : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  refine ⟨s1, hsd, ?_, ?_⟩
  · rw [← hs, ← hi]; exact hre
  · rw [hq, ← hi, storageRemoveHost_erase he]

/-- **`storage_remove`, metered**, as a read contract: with the key's `kl` bytes `key` at `kp`,
over a host whose storage accounting `s` is a canonical trie linked to its `storage` (`hlink`),
and not a view call, the call returns `1` (and sets register `r` to the old value) or `0`, leaves
the host as `StorageRemovePost`, and uses at most `storageRemoveUse` gas. -/
theorem storageRemove_readContract (extra : Nat) (h : NearState) (kl kp r : UInt64) (key : List UInt8)
    (s : State) {C b : Nat} (hkl : kl ≠ u64Max) (hkn : key.length = kl.toNat) (hkpos : 0 < kl.toNat)
    (hview : h.context.isView = false)
    (hacc : h.storageAccounting = some s)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal s (contractKey h.context.currentAccountId key))
    (hproof : ProofBudget h s b)
    (hbud : removeProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ b)
    (hreg : ∀ v, h.storage key = some v → r ≠ u64Max → withinLimit h.config.maxRegisterLen v.length = true) :
    ReadContractP (metered extra "storage_remove" storageRemoveFn).toHostFn h (StorageRemovePost extra h key r s)
      [.i64 kl, .i64 kp, .i64 r] (storageReadResult (h.storage key)) kp.toNat key
      (storageRemoveUse h key kl.toNat) C := by
  intro host mem hwf he hrd hu hmb hpp
  have fsa : host.storageAccounting = h.storageAccounting := erase_field he NearState.storageAccounting fun _ => rfl
  have fid : host.context.currentAccountId = h.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have fview : host.context.isView = h.context.isView :=
    erase_field he (fun x : NearState => x.context.isView) fun _ => rfl
  have fcfg : host.config = h.config := erase_field he NearState.config fun _ => rfl
  have fsto : host.storage = h.storage := erase_field he NearState.storage fun _ => rfl
  have fpsz : host.storageProofSize = h.storageProofSize := erase_field he NearState.storageProofSize fun _ => rfl
  have hin : kp.toNat + kl.toNat ≤ mem.size * 65536 := by
    have := (hrd (kl.toNat - 1) (by omega)).1
    unfold Memory.byteSize at this
    show _ ≤ mem.pages.size * 65536
    unfold pageSize at this
    omega
  have hkey : getMemOrReg { mem, host } kp kl = some key := by
    simp only [getMemOrReg, hkl, ite_false]
    rw [if_neg (by show ¬ _ > mem.pages.size * 65536; show ¬ _ > mem.size * 65536; omega)]
    rw [← hkn]
    exact congrArg some (readList_eq fun k hk => (hrd k hk).2)
  rw [← storageRemoveUse_erase he] at hu ⊢
  obtain ⟨host', hinv, hq, hused, hmb', hpp'⟩ := storageRemove_ok extra { mem, host } kl kp r key s (C := C)
    hkl (by rw [← hview]; exact fview) hkey hkn (by rw [fsa]; exact hacc) (by rw [fcfg]; exact hlim)
    hb hz (by rw [fsto, fid]; exact hlink) (hproof.congr fpsz fcfg)
    (by rw [fid, fsto]; exact hbud) (by rw [fsto, fcfg]; exact hreg) hu hmb hpp
  refine ⟨host', ?_, storageRemovePost_erase he hq, hused, hmb', hpp'⟩
  simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
  rw [show host.storage key = h.storage key by rw [fsto]]

/-! ## The overlay after a removal -/

open private insert from NearInterface.TrieOverlay in
theorem remove_prospective (s : State) (k : List UInt8) :
    (s.remove k).prospective = (k, none) :: s.prospective.filter (·.1 != k) := rfl

theorem viewVal_remove_same (s : State) (k : List UInt8) : viewVal (s.remove k) k = none := by
  simp [viewVal, remove_prospective]

theorem viewVal_remove_other (s : State) {k k' : List UInt8} (hk : k' ≠ k) :
    viewVal (s.remove k) k' = viewVal s k' := by
  have hf : (s.remove k).prospective.find? (·.1 == k') = s.prospective.find? (·.1 == k') := by
    rw [remove_prospective, List.find?_cons_of_neg (by simpa using Ne.symm hk)]
    rw [List.find?_filter]
    congr 1
    funext a
    by_cases ha : a.1 = k'
    · subst ha; simp [hk]
    · simp [ha]
  unfold viewVal
  rw [hf]
  rfl

theorem Canon.remove {s : State} (hc : Canon s) (k : List UInt8) : Canon (s.remove k) := hc

theorem storageRemoveHost_storage (extra : Nat) (h : NearState) (key : List UInt8) (r : UInt64) (s2 : State) :
    (storageRemoveHost extra h key r s2).storage = fun k => if k = key then none else h.storage k := by
  unfold storageRemoveHost logRemove removeRegs
  split
  · simp only [NearState.invalidateIterators, NearState.removeStorage]
    unfold storageReadRegs
    split <;> (try split) <;> rfl
  · rename_i hn
    funext k
    by_cases hk : k = key
    · subst hk; simp [hn]
    · simp [hk]

theorem storageRemoveHost_context_id (extra : Nat) (h : NearState) (key : List UInt8) (r : UInt64)
    (s2 : State) : (storageRemoveHost extra h key r s2).context.currentAccountId = h.context.currentAccountId := by
  unfold storageRemoveHost logRemove
  simp only
  rw [removeRegs_context]

theorem storageRemoveHost_acc (extra : Nat) (h : NearState) (key : List UInt8) (r : UInt64) (s2 : State) :
    (storageRemoveHost extra h key r s2).storageAccounting = some s2 ∧
      (storageRemoveHost extra h key r s2).storageProofSize = h.storageProofSize ∧
      (storageRemoveHost extra h key r s2).config = h.config := by
  unfold storageRemoveHost logRemove removeRegs
  split
  · simp only [NearState.invalidateIterators, NearState.removeStorage]
    unfold storageReadRegs
    split <;> (try split) <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- A removal keeps the host linked to the overlay. -/
theorem StorageLink.remove {h : NearState} {s s1 : State} (hl : StorageLink h s) (hsd : SameData s s1)
    (extra : Nat) (key : List UInt8) (r : UInt64) :
    StorageLink (storageRemoveHost extra h key r (s1.remove (contractKey h.context.currentAccountId key)))
      (s1.remove (contractKey h.context.currentAccountId key)) := by
  intro k
  rw [storageRemoveHost_storage, storageRemoveHost_context_id]
  by_cases hk : k = key
  · subst hk; simp [viewVal_remove_same]
  · simp only [hk, ite_false]
    rw [viewVal_remove_other _ (fun he => hk (contractKey_inj he)), viewVal_sameData hsd]
    exact hl k

/-- What `storage_remove` leaves meets the hypotheses of the next storage call: the accounting is
a canonical trie linked to the storage, with the budget spent. -/
theorem StorageRemovePost.next {extra : Nat} {h host' : NearState} {key : List UInt8} {r : UInt64}
    {s : State} {b : Nat} (hq : StorageRemovePost extra h key r s host') (hc : Canon s) (hl : StorageLink h s)
    (hproof : ProofBudget h s b)
    (hbud : removeProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ b) :
    ∃ s2, host'.storageAccounting = some s2 ∧ Canon s2 ∧ StorageLink host' s2 ∧
      ProofBudget host' s2 (b - removeProofCost (contractKey h.context.currentAccountId key) (h.storage key)) ∧
      erase host' = erase (storageRemoveHost extra h key r s2) := by
  obtain ⟨s1, hsd, hre, he⟩ := hq
  have ha := storageRemoveHost_acc extra h key r (s1.remove (contractKey h.context.currentAccountId key))
  refine ⟨_, ?_, (hc.sameData hsd).remove _, (hl.remove hsd extra key r).erase he, ?_, he⟩
  · rw [erase_field he NearState.storageAccounting fun _ => rfl]; exact ha.1
  · refine (hproof.reach hre hbud).congr ?_ ?_
    · rw [erase_field he NearState.storageProofSize fun _ => rfl]; exact ha.2.1
    · rw [erase_field he NearState.config fun _ => rfl]; exact ha.2.2

end NearLogic
