import NearLogic.Hosts.StorageRead
import NearLogic.Relax
import NearLogic.CallPred2

/-!
# `storage_write`, metered

The host contract of metered `storage_write(key_len, key_ptr, value_len, value_ptr, register_id)`
with the key and the value in memory, over a host whose storage accounting is an overlay on a
canonical trie linked to its `storage` through the overlay's view (`viewVal`), as for
`storage_read` (`StorageRead.lean`).

* `prepareStorageCallAux_write`: the storage phase for a mutation succeeds. It looks the raw key
  up with `accountNodes = true` (`storage_lookup_view`), bills the evicted bytes, dereferences the
  old value, bills the trie nodes (at most `2·|rawKey| + 2` at the dearer node cost), stages the
  write (`State.set`), and the recorded-proof check after it passes: the operations
  (`ProofReach`: lookup, dereference, set) record at most `writeProofCost`, within the budget.
* `storageWrite_ok`: the whole metered call: returns `storageReadResult` of the old value, the old
  value in register `r` (`storageReadRegs`), the new value stored, the usage updated
  (`writeUsage`, as `updateStorageUsage`) and the write logged (`storageLog`):
  `storageWriteHost`, up to gas and with the accounting `s1.set rawKey val` for some `s1` with the
  data of `s` (`StorageWritePost`). The gas is at most `storageWriteUse`.
* `storageWrite_readContract`: the call as a `ReadContractP2` (two byte ranges,
  `CallPred2.lean`).
* `StorageWritePost.next`: what the write leaves meets the next storage call's hypotheses: a
  canonical overlay (`Canon`) linked to the storage (`StorageLink`), with the proof budget spent
  by `writeProofCost` (`ProofBudget.reach`).

The call must not be a view call: `storage_write` is prohibited in views.
-/

namespace NearLogic

open Wasm Wasm.Near Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-- `dereference` adds at most one access, to either counter. -/
theorem dereference_counters_le {s s' : State} {p : ValuePointer} {v : List UInt8}
    (h : Near.TrieOverlay.dereference s p = .ok (s', v)) :
    ∃ d m, s'.accounting.disk = s.accounting.disk + d ∧ s'.accounting.mem = s.accounting.mem + m ∧
      d + m ≤ 1 := by
  cases p with
  | memory bytes => cases h; exact ⟨0, 0, rfl, rfl, by omega⟩
  | trie root r =>
    obtain ⟨d, m, hd, hm, hdm⟩ := dereference_counters h
    exact ⟨d, m, hd, hm, by omega⟩

/-- `ext` charges within the credits: they succeed, change only the gas cell, and leave the
promise gas alone. -/
theorem bill_ext (ns : NearState) (cs : List Charge) (hx : ExtOnly cs) {C : Nat}
    (h1 : ns.gas.used + chargesUse ns cs ≤ C) (h2 : C ≤ ns.gas.maxBurnt) (h3 : C ≤ ns.gas.prepaid) :
    ∃ ns', applyCharges ns cs = (ns', none) ∧ ChargedTo ns ns' (chargesUse ns cs) ∧
      ns'.gas.promises = ns.gas.promises := by
  obtain ⟨ok, ch⟩ := applyCharges_ok ns cs h1 h2 h3
  refine ⟨(applyCharges ns cs).1, ?_, ch, applyCharges_ext_promises ns cs hx h1 h2 h3⟩
  rw [← ok]

theorem extOnly_trie (d m : Nat) : ExtOnly (trieNodeCharges d m) := by
  intro c hc; simp only [trieNodeCharges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact ⟨_, _, rfl⟩

theorem extOnly_one (n : String) (t : Nat) : ExtOnly [.ext n t] := by
  intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc; exact ⟨_, _, rfl⟩

/-- Within the budget, the VM's check after a sequence of operations passes. -/
theorem recordedStorageError_reach {h : NearState} {s t : State} {c b : Nat} (hp : ProofBudget h s b)
    (hst : ProofReach s t c) (hcb : c ≤ b) : recordedStorageError h t = none := by
  unfold recordedStorageError
  cases hs : h.storageProofSize with
  | none => rfl
  | some size =>
    simp only
    rw [if_neg (Nat.not_lt.mpr (hp size hs t c hst hcb))]

/-- A sequence of operations spends its share of the budget. -/
theorem ProofBudget.reach {h : NearState} {s t : State} {c b : Nat} (hp : ProofBudget h s b)
    (hst : ProofReach s t c) (hcb : c ≤ b) : ProofBudget h t (b - c) := by
  intro size hsz u c' hr hc'
  exact hp size hsz u (c + c') (hst.trans hr) (by omega)

/-- The gas the storage phase of `storage_write` may burn, for the raw trie key
`rawKey` and the old value `old`: the evicted bytes, then the nodes of the lookup and
the dereference. -/
def storageWritePhaseUse (h : NearState) (rawKey : List UInt8) (old : Option (List UInt8)) : Nat :=
  (2 * rawKey.length + 2) * trieNodeMax h +
    ((old.map fun v => chargesUse h [.ext "storage_write_evicted_byte" v.length]).getD 0)

/-- The most a `storage_write` of `rawKey` over the old value `old` records. -/
def writeProofCost (rawKey : List UInt8) (old : Option (List UInt8)) : Nat :=
  lookupProofBound rawKey + ((old.map List.length).getD 0)

theorem prepareStorageCallAux_write (before : HostStore NearState) (kl kp vl vp r : UInt64)
    (key val rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before kp kl = some key)
    (hval : getMemOrReg before vp vl = some val)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : writeProofCost rawKey (before.host.storage key) ≤ b)
    (h1 : before.host.gas.used + storageWritePhaseUse before.host rawKey (before.host.storage key) ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ after s1, prepareStorageCallAux "storage_write" before [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] =
        (after, none) ∧
      after.host.storageAccounting = some (s1.set rawKey val) ∧ SameData s s1 ∧
      ProofReach s (s1.set rawKey val) (writeProofCost rawKey (before.host.storage key)) ∧
      after.host.gas.burnt ≤
        before.host.gas.burnt + storageWritePhaseUse before.host rawKey (before.host.storage key) ∧
      after.host.gas.promises = before.host.gas.promises := by
  obtain ⟨s', p, hget, hsd, ⟨d, m, hd, hm, hdm⟩, hpres, hder⟩ :=
    storage_lookup_view (k := rawKey) true hb hz
  have hcon : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "storage_write" = true := by decide
  have e1 : ("storage_write" == "storage_write") = true := by decide
  have e2 : ("storage_write" == "storage_remove") = false := by decide
  have e3 : ("storage_write" != "storage_has_key") = true := by decide
  have e4 : ("storage_write" == "storage_read") = false := by decide
  have hlk : ∀ l, before.host.config.maxStorageKeyLen = some l → ¬ key.length > l := by
    intro l hl; rw [hl] at hlim; simpa [withinLimit] using hlim
  rw [← hlink] at hpres hder
  have hpres' : (p.isSome != (before.host.storage key).isSome) = false := by
    rw [hpres]; exact bne_self_eq_false _
  have hfb : (2 * rawKey.length + 2) * trieNodeMax before.host ≤
      storageWritePhaseUse before.host rawKey (before.host.storage key) := by
    unfold storageWritePhaseUse; omega
  simp only [prepareStorageCallAux, hcon, hacc, argU64, Id.run]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, hkey, hval, e1, e2, e3, e4,
    Bool.or_false, Bool.true_or, ite_true, Bool.false_eq_true, ite_false]
  rw [← hraw, hget]
  split
  on_goal 1 => rename_i lim hml; rw [if_neg (hlk lim hml)]
  all_goals
    dsimp only
    rw [hpres']
    simp only [Bool.false_eq_true, ite_false]
    set ns0 : NearState := { before.host with storageAccounting := some s' } with hns0
    have hu0 : ns0.gas = before.host.gas := rfl
    have hb0 : ns0.gas.burnt = before.host.gas.burnt := rfl
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
      rw [hdd, hmm]
      have htc : chargesUse ns0 (trieNodeCharges d m) ≤ (2 * rawKey.length + 2) * trieNodeMax before.host :=
        Nat.le_trans (trieNodeCharges_use ns0 d m) (Nat.mul_le_mul_right _ (by omega))
      rw [hv] at hfb h1
      obtain ⟨ns1, hA, ch1, pr1⟩ := bill_ext ns0 (trieNodeCharges d m) (extOnly_trie d m) (C := C)
        (by rw [hu0]; omega) h2 h3
      simp only [trieNodeCharges] at hA
      rw [hA]
      have hreach : ProofReach s (s'.set rawKey val) (writeProofCost rawKey none) := by
        have := ProofReach.step (ProofStep.lookup hget) (ProofReach.step (ProofStep.set s' rawKey val)
          (ProofReach.refl _))
        simpa [writeProofCost] using this
      have hpsz : ns1.storageProofSize = before.host.storageProofSize :=
        erase_field ch1.erase NearState.storageProofSize fun _ => rfl
      have hrec : recordedStorageError { ns1 with storageAccounting := some (s'.set rawKey val) }
          (s'.set rawKey val) = none :=
        recordedStorageError_reach (hproof.congr hpsz ch1.config) hreach (by rw [hv] at hbud; exact hbud)
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hrec]
      refine ⟨_, s', rfl, rfl, hsd, hreach, ?_, pr1⟩
      have hu1 := ch1.used
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
      have hev : chargesUse ns0 [Charge.ext "storage_write_evicted_byte" v.length] =
          chargesUse before.host [Charge.ext "storage_write_evicted_byte" v.length] := rfl
      have hph : storageWritePhaseUse before.host rawKey (some v) = (2 * rawKey.length + 2) * trieNodeMax before.host +
          chargesUse before.host [Charge.ext "storage_write_evicted_byte" v.length] := rfl
      obtain ⟨ns1, hA1, ch1, pr1⟩ := bill_ext ns0 [Charge.ext "storage_write_evicted_byte" v.length]
        (extOnly_one _ _) (C := C) (by rw [hu0, hev]; omega) h2 h3
      rw [hA1]
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hd2]
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
      set ns1' : NearState := { ns1 with storageAccounting := some s'' } with hns1'
      have hdd : s''.accounting.disk - s.accounting.disk = d + d2 := by omega
      have hmm : s''.accounting.mem - s.accounting.mem = m + m2 := by omega
      rw [hdd, hmm]
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
      have hreach : ProofReach s (s''.set rawKey val) (writeProofCost rawKey (some v)) := by
        have := ProofReach.step (ProofStep.lookup hget) (ProofReach.step (ProofStep.dereference hd2)
          (ProofReach.step (ProofStep.set s'' rawKey val) (ProofReach.refl _)))
        simpa [writeProofCost] using this
      have hpsz : ns2.storageProofSize = before.host.storageProofSize :=
        (erase_field ch2.erase NearState.storageProofSize fun _ => rfl).trans
          (erase_field ch1.erase NearState.storageProofSize fun _ => rfl)
      have hcf : ns2.config = before.host.config := ch2.config.trans ch1.config
      have hrec : recordedStorageError { ns2 with storageAccounting := some (s''.set rawKey val) }
          (s''.set rawKey val) = none :=
        recordedStorageError_reach (hproof.congr hpsz hcf) hreach hbud
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hrec]
      refine ⟨_, s'', rfl, rfl, ?_, hreach, ?_, ?_⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hsd
        obtain ⟨b1, b2, b3, b4⟩ := hsd2
        exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩
      · have hu2 := ch2.used
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

/-- The storage phase of `storage_write`, as the metered wrapper sees it: only the accounting
(the old one up to its caches, with the write staged), the burnt gas and the gas profile change. -/
theorem prepareStorageCall_write (before : HostStore NearState) (kl kp vl vp r : UInt64)
    (key val rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before kp kl = some key)
    (hval : getMemOrReg before vp vl = some val)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : writeProofCost rawKey (before.host.storage key) ≤ b)
    (h1 : before.host.gas.used + storageWritePhaseUse before.host rawKey (before.host.storage key) ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ s1 bt p, prepareStorageCall "storage_write" before [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] =
        ({ before with host := phaseHost before.host (s1.set rawKey val) bt p }, none) ∧ SameData s s1 ∧
      ProofReach s (s1.set rawKey val) (writeProofCost rawKey (before.host.storage key)) ∧
      bt ≤ before.host.gas.burnt + storageWritePhaseUse before.host rawKey (before.host.storage key) := by
  obtain ⟨after, s1, haux, hsa, hsd, hre, hb', -⟩ :=
    prepareStorageCallAux_write before kl kp vl vp r key val rawKey s hraw hacc hkey hval hlim hb hz hlink
      hproof hbud h1 h2 h3
  refine ⟨s1, after.host.gas.burnt, after.host.gasProfile, ?_, hsd, hre, hb'⟩
  simp only [prepareStorageCall, haux, hsa, Option.isNone_none, ite_true, phaseHost]

/-! ## The metered call -/

/-- The charges of `storage_write` before it runs, for a key of `k` bytes and a value of `v`
bytes in memory. -/
def storageWriteBeforeCharges (k v : Nat) : List Charge :=
  [.ext "base", .ext "storage_write_base", .ext "read_memory_base", .ext "read_memory_byte" k,
    .ext "read_memory_base", .ext "read_memory_byte" v, .ext "storage_write_key_byte" k,
    .ext "storage_write_value_byte" v]

theorem storageMutationPlan_write (st : HostStore NearState) (kl kp vl vp r : UInt64) (key val : List UInt8)
    (hkl : kl ≠ u64Max) (hvl : vl ≠ u64Max)
    (hkey : getMemOrReg st kp kl = some key) (hval : getMemOrReg st vp vl = some val)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hvlim : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hacc : st.host.storageAccounting.isSome = true) :
    storageMutationPlan? "storage_write" st [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] =
      some { charges := [.ext "base", .ext "storage_write_base", .ext "read_memory_base",
        .ext "read_memory_byte" kl.toNat, .ext "read_memory_base", .ext "read_memory_byte" vl.toNat,
        .ext "storage_write_key_byte" key.length, .ext "storage_write_value_byte" val.length] } := by
  have hlk : ∀ l, st.host.config.maxStorageKeyLen = some l → ¬ key.length > l := by
    intro l hl; rw [hl] at hlim; simpa [withinLimit] using hlim
  have hvk : ∀ l, st.host.config.maxStorageValueLen = some l → ¬ val.length > l := by
    intro l hl; rw [hl] at hvlim; simpa [withinLimit] using hvlim
  have hsv : storageValueCharges st "storage_write_evicted_byte" key = [] := by
    unfold storageValueCharges
    cases h : st.host.storageAccounting with
    | none => rw [h] at hacc; cases hacc
    | some _ => simp
  simp only [storageMutationPlan?, argU64, List.getElem?_cons_succ, List.getElem?_cons_zero,
    hkey, hval, readSpan, hkl, hvl, ite_false, hsv, List.append_nil]
  simp only [show ("storage_write" != "storage_write") = false by decide,
    show ("storage_write" == "storage_write") = true by decide, Bool.false_and, Bool.false_eq_true,
    ite_false, ite_true]
  cases hk : st.host.config.maxStorageKeyLen with
  | none =>
    cases hv : st.host.config.maxStorageValueLen with
    | none => rfl
    | some lv => simp [hvk lv hv]
  | some lk =>
    simp only [hlk lk hk, ite_false]
    cases hv : st.host.config.maxStorageValueLen with
    | none => rfl
    | some lv => simp [hvk lv hv]

theorem chargesBefore_storageWrite (st : HostStore NearState) (kl kp vl vp r : UInt64) (key val : List UInt8)
    (hkl : kl ≠ u64Max) (hvl : vl ≠ u64Max)
    (hkey : getMemOrReg st kp kl = some key) (hval : getMemOrReg st vp vl = some val)
    (hkn : key.length = kl.toNat) (hvn : val.length = vl.toNat)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hvlim : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hacc : st.host.storageAccounting.isSome = true) :
    chargesBefore "storage_write" st [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] =
      storageWriteBeforeCharges kl.toNat vl.toNat := by
  unfold chargesBefore
  rw [storageMutationPlan_write st kl kp vl vp r key val hkl hvl hkey hval hlim hvlim hacc, hkn, hvn]
  rfl

theorem preInvokeError_storageWrite (st : HostStore NearState) (kl kp vl vp r : UInt64) (key val : List UInt8)
    (hkl : kl ≠ u64Max) (hvl : vl ≠ u64Max)
    (hkey : getMemOrReg st kp kl = some key) (hval : getMemOrReg st vp vl = some val)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hvlim : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hacc : st.host.storageAccounting.isSome = true) :
    preInvokeError "storage_write" st [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] = none := by
  unfold preInvokeError invocationArgumentError
  rw [storageMutationPlan_write st kl kp vl vp r key val hkl hvl hkey hval hlim hvlim hacc]
  simp [allocatesPromise, functionCallInputError, functionCallInputs?]

/-- `storage_write` itself, after the metering: the old value to register `r`, the new value
stored. -/
theorem storageWriteFn_invoke (st : HostStore NearState) (kl kp vl vp r : UInt64) (key val : List UInt8)
    (hview : st.host.context.isView = false)
    (hkey : getMemOrReg st kp kl = some key) (hval : getMemOrReg st vp vl = some val)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hvlim : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hreg : ∀ v, st.host.storage key = some v → r ≠ u64Max →
      withinLimit st.host.config.maxRegisterLen v.length = true) :
    storageWriteFn.invoke st [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] =
      .Return (storageReadResult (st.host.storage key))
        { st with host := ((storageReadRegs st.host r (st.host.storage key)).setStorage key val).invalidateIterators } := by
  simp only [storageWriteFn, disallowInView, hview, Bool.false_eq_true, ite_false, hkey, hval, checkDataLimit,
    hlim, hvlim, ite_true]
  cases hv : st.host.storage key with
  | none => rfl
  | some v =>
    simp only [checkedSetRegister?, storageReadResult, storageReadRegs]
    by_cases hr : r = u64Max
    · simp [hr]
    · simp [hr, hreg v hv hr]

/-- The contract's storage usage after writing `val` under `key` over `old`
(`updateStorageUsage`): a new record costs the key, the value and `extra`; an overwrite the
value difference. -/
def writeUsage (extra : Nat) (key val : List UInt8) (old : Option (List UInt8)) (usage : Nat) : Nat :=
  match old with
  | none => usage + key.length + val.length + extra
  | some o => usage + val.length - o.length

/-- The usage and log update of a storage write. -/
def logWrite (extra : Nat) (old : Option (List UInt8)) (usage : Nat) (key val : List UInt8) (x : NearState) :
    NearState :=
  { x with
    context := { x.context with storageUsage := UInt64.ofNat (writeUsage extra key val old usage) }
    storageLog := { key, existed := old.isSome, value := some val } :: x.storageLog }

theorem erase_logWrite (extra : Nat) (old : Option (List UInt8)) (usage : Nat) (key val : List UInt8)
    (x : NearState) : erase (logWrite extra old usage key val x) = logWrite extra old usage key val (erase x) := rfl

/-- What `storage_write(key, val)` into register `r` leaves of `h`, up to gas, once its
accounting is `s2`: the old value in register `r` (as `storage_read`), the new value stored,
the iterators invalidated, the storage usage updated and the write logged. -/
def storageWriteHost (extra : Nat) (h : NearState) (key val : List UInt8) (r : UInt64) (s2 : State) :
    NearState :=
  logWrite extra (h.storage key) h.context.storageUsage.toNat key val
    (((storageReadRegs { h with storageAccounting := some s2 } r (h.storage key)).setStorage key val).invalidateIterators)

/-- The charges after `storage_write`: writing the old value to the register. -/
def storageWriteAfter (old : Option (List UInt8)) : List Charge :=
  (old.map fun v => writeReg v.length).getD []

theorem chargesAfter_storageWrite (before st : HostStore NearState) (kl kp vl vp r : UInt64) (key : List UInt8)
    (hkey : getMemOrReg before kp kl = some key) :
    chargesAfter "storage_write" before st [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] =
      storageWriteAfter (before.host.storage key) := by
  simp only [chargesAfter, argU64, List.getElem?_cons_succ, List.getElem?_cons_zero, hkey]
  cases before.host.storage key <;> rfl

/-- Post-call metering of `storage_write`: the after-charges, then the usage and the log. -/
theorem finish_storageWrite (extra : Nat) (before st : HostStore NearState) (kl kp vl vp r : UInt64)
    (key val : List UInt8) (vals : List Value)
    (hkey : getMemOrReg before kp kl = some key) (hst : st.host.storage key = some val)
    (h : (applyCharges st.host (storageWriteAfter (before.host.storage key))).2 = none) :
    finishMeteredCall extra "storage_write" before [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] (.Return vals st) =
      .Return vals { st with host := (logWrite extra (before.host.storage key)
        (applyCharges st.host (storageWriteAfter (before.host.storage key))).1.context.storageUsage.toNat key val
        (applyCharges st.host (storageWriteAfter (before.host.storage key))).1) } := by
  simp only [finishMeteredCall]
  rw [chargesAfter_storageWrite before st kl kp vl vp r key hkey]
  have hsA : (applyCharges st.host (storageWriteAfter (before.host.storage key))).1.storage = st.host.storage :=
    erase_field (applyCharges_erase _ _) NearState.storage fun _ => rfl
  generalize applyCharges st.host (storageWriteAfter (before.host.storage key)) = A at h hsA ⊢
  obtain ⟨ns, e⟩ := A
  simp only at h
  subst h
  have hd : deductDeposit "storage_write" before { st with host := ns }
      [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] = ({ st with host := ns }, none) := by
    simp (config := { decide := true }) [deductDeposit, promiseDeposit?]
  have ha : actionMethodEncodingError "storage_write" before [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] = none := by
    simp (config := { decide := true }) [actionMethodEncodingError, actionMethodBytes?, functionCallInputs?]
  simp only [hd, ha]
  simp only at hsA
  have hns : ns.storage key = some val := by rw [hsA]; exact hst
  simp only [updateStorageUsage, hns, argU64, List.getElem?_cons_succ, List.getElem?_cons_zero, hkey]
  cases before.host.storage key <;> rfl

/-- What `storage_write(key, val)` into register `r` leaves, up to gas, from `h` with accounting
`s`: the host as `storageWriteHost`, whose accounting is the write staged on one with the data of
`s`, reached by operations recording at most `writeProofCost`. -/
def StorageWritePost (extra : Nat) (h : NearState) (key val : List UInt8) (r : UInt64) (s : State)
    (host' : NearState) : Prop :=
  ∃ s1, SameData s s1 ∧
    ProofReach s (s1.set (contractKey h.context.currentAccountId key) val)
      (writeProofCost (contractKey h.context.currentAccountId key) (h.storage key)) ∧
    erase host' = erase (storageWriteHost extra h key val r
      (s1.set (contractKey h.context.currentAccountId key) val))

/-- The gas `storage_write` of a `k`-byte key and a `v`-byte value may use: the charges before,
the storage phase (`storageWritePhaseUse`), and writing the old value to the register. -/
def storageWriteUse (h : NearState) (key : List UInt8) (k v : Nat) : Nat :=
  chargesUse h (storageWriteBeforeCharges k v) +
    storageWritePhaseUse h (contractKey h.context.currentAccountId key) (h.storage key) +
    chargesUse h (storageWriteAfter (h.storage key))

theorem storageReadRegs_context (h : NearState) (r : UInt64) (val : Option (List UInt8)) :
    (storageReadRegs h r val).context = h.context := by
  unfold storageReadRegs; split
  · split <;> rfl
  · rfl

theorem erase_setStorage_inv (x : NearState) (key val : List UInt8) :
    erase ((x.setStorage key val).invalidateIterators) = ((erase x).setStorage key val).invalidateIterators := rfl

/-- The metered call on a store: the charges before, the storage phase, the host function and
the charges after all succeed within the credits. -/
theorem storageWrite_ok (extra : Nat) (st : HostStore NearState) (kl kp vl vp r : UInt64) (key val : List UInt8)
    (s : State) {C b : Nat} (hkl : kl ≠ u64Max) (hvl : vl ≠ u64Max)
    (hview : st.host.context.isView = false)
    (hkey : getMemOrReg st kp kl = some key) (hval : getMemOrReg st vp vl = some val)
    (hkn : key.length = kl.toNat) (hvn : val.length = vl.toNat)
    (hacc : st.host.storageAccounting = some s)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hvlim : withinLimit st.host.config.maxStorageValueLen val.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : st.host.storage key = viewVal s (contractKey st.host.context.currentAccountId key))
    (hproof : ProofBudget st.host s b)
    (hbud : writeProofCost (contractKey st.host.context.currentAccountId key) (st.host.storage key) ≤ b)
    (hreg : ∀ v, st.host.storage key = some v → r ≠ u64Max →
      withinLimit st.host.config.maxRegisterLen v.length = true)
    (h1 : st.host.gas.used + storageWriteUse st.host key kl.toNat vl.toNat ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "storage_write" storageWriteFn).invoke st [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] =
        .Return (storageReadResult (st.host.storage key)) { mem := st.mem, host := host' } ∧
      StorageWritePost extra st.host key val r s host' ∧
      host'.gas.used ≤ st.host.gas.used + storageWriteUse st.host key kl.toNat vl.toNat ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  have hdep : deprecatedRuntimeHost "storage_write" = false := by decide
  have hu := h1
  unfold storageWriteUse at hu
  have haccs : st.host.storageAccounting.isSome = true := by rw [hacc]; rfl
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (storageWriteBeforeCharges kl.toNat vl.toNat) (C := C)
    (by omega) h2 h3
  simp only [metered, hdep, hview, Bool.false_and, Bool.false_eq_true, ite_false]
  rw [chargesBefore_storageWrite st kl kp vl vp r key val hkl hvl hkey hval hkn hvn hlim hvlim haccs]
  generalize hac : applyCharges st.host (storageWriteBeforeCharges kl.toNat vl.toNat) = ac at hok hch
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
  have hval1 : getMemOrReg { mem := st.mem, host := afterCharges ns } vp vl = some val :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := afterCharges ns }) hvl rfl).trans hval
  erw [preInvokeError_storageWrite { mem := st.mem, host := afterCharges ns } kl kp vl vp r key val hkl hvl
    hkey1 hval1 (by rw [fcfg]; exact hlim) (by rw [fcfg]; exact hvlim) (by rw [fsa]; exact haccs)]
  simp only
  show ∃ host', invokeStorageCall extra "storage_write" storageWriteFn
    { mem := st.mem, host := afterCharges ns } [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] = _ ∧ _
  have hphase : storageWritePhaseUse (afterCharges ns) (contractKey st.host.context.currentAccountId key)
      ((afterCharges ns).storage key) =
      storageWritePhaseUse st.host (contractKey st.host.context.currentAccountId key) (st.host.storage key) := by
    simp only [storageWritePhaseUse, trieNodeMax, fext, fsto]
    cases st.host.storage key <;> simp [chargesUse_of ffee fext]
  obtain ⟨s1, bt, p, hpre, hsd, hre, hbb⟩ := prepareStorageCall_write { mem := st.mem, host := afterCharges ns }
    kl kp vl vp r key val (contractKey st.host.context.currentAccountId key) s (C := C) (by rw [fid])
    (by rw [fsa]; exact hacc) hkey1 hval1 (by rw [fcfg]; exact hlim) hb hz
    (by rw [fsto]; exact hlink) (hproof.congr fpsz fcfg) (by rw [fsto]; exact hbud)
    (by rw [hphase, hgas1, hch.used]; omega) (by rw [hgas1, hch.maxBurnt]; exact h2)
    (by rw [hgas1, hch.prepaid]; exact h3)
  rw [hphase] at hbb
  have hbb' : bt ≤ ns.gas.burnt + storageWritePhaseUse st.host (contractKey st.host.context.currentAccountId key)
      (st.host.storage key) := hbb
  rw [fsto] at hre
  simp only [invokeStorageCall, hpre]
  set s2 := s1.set (contractKey st.host.context.currentAccountId key) val with hs2
  set H2 := phaseHost (afterCharges ns) s2 bt p with hH2
  have hkey2 : getMemOrReg { mem := st.mem, host := H2 } kp kl = some key :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := H2 }) hkl rfl).trans hkey
  have hval2 : getMemOrReg { mem := st.mem, host := H2 } vp vl = some val :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := H2 }) hvl rfl).trans hval
  have hsto2 : H2.storage = st.host.storage := fsto
  have hcfg2 : H2.config = st.host.config := fcfg
  have hview2 : H2.context.isView = false := by rw [← hview]; exact fview
  rw [storageWriteFn_invoke { mem := st.mem, host := H2 } kl kp vl vp r key val hview2 hkey2 hval2
    (by rw [hcfg2]; exact hlim) (by rw [hcfg2]; exact hvlim) (by rw [hcfg2, hsto2]; exact hreg)]
  rw [hsto2]
  set H3 := ((storageReadRegs H2 r (st.host.storage key)).setStorage key val).invalidateIterators with hH3
  have hst3 : H3.storage key = some val := by
    simp [hH3, NearState.invalidateIterators, NearState.setStorage]
  set cs := storageWriteAfter (st.host.storage key) with hcs
  have hfe3 := storageReadRegs_fees H2 r (st.host.storage key)
  have hcu : chargesUse H3 cs = chargesUse st.host cs :=
    chargesUse_of (hfe3.1.trans ffee) (hfe3.2.trans fext) cs
  have hg3 : H3.gas = { ns.gas with burnt := bt } := by
    rw [hH3]
    show (storageReadRegs H2 r (st.host.storage key)).gas = _
    rw [storageReadRegs_gas]; rfl
  have hn := hch.used
  simp only [Near.GasCounter.used] at hn hu
  obtain ⟨ok4, ch4⟩ := applyCharges_ok H3 cs (C := C)
    (by rw [hcu, hg3]; simp only [Near.GasCounter.used]; omega)
    (by rw [hg3]; show C ≤ ns.gas.maxBurnt; rw [hch.maxBurnt]; exact h2)
    (by rw [hg3]; show C ≤ ns.gas.prepaid; rw [hch.prepaid]; exact h3)
  have hfin := finish_storageWrite extra { mem := st.mem, host := H2 } { mem := st.mem, host := H3 }
    kl kp vl vp r key val (storageReadResult (st.host.storage key)) hkey2 hst3 (by rw [hsto2]; exact ok4)
  simp only [hsto2] at hfin
  rw [hfin]
  have hus : (applyCharges H3 cs).1.context.storageUsage = st.host.context.storageUsage := by
    have e3 : erase (applyCharges H3 cs).1 = erase H3 := ch4.erase
    rw [erase_field e3 (fun x : NearState => x.context.storageUsage) fun _ => rfl]
    rw [hH3]
    show (storageReadRegs H2 r (st.host.storage key)).context.storageUsage = _
    rw [storageReadRegs_context]
    exact erase_field he1 (fun x : NearState => x.context.storageUsage) fun _ => rfl
  refine ⟨_, rfl, ⟨s1, hsd, hre, ?_⟩, ?_, ?_, ?_⟩
  · rw [erase_logWrite, ch4.erase, hus, hH3, erase_setStorage_inv, erase_storageReadRegs]
    unfold storageWriteHost
    rw [erase_logWrite, erase_setStorage_inv, erase_storageReadRegs]
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

theorem storageWriteUse_erase {h h' : NearState} (he : erase h = erase h') (key : List UInt8) (k v : Nat) :
    storageWriteUse h key k v = storageWriteUse h' key k v := by
  have hf : h.fees = h'.fees := erase_field he NearState.fees fun _ => rfl
  have hx : h.extCosts = h'.extCosts := erase_field he NearState.extCosts fun _ => rfl
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  have hi : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  unfold storageWriteUse storageWritePhaseUse trieNodeMax
  rw [hs, hi, hx, chargesUse_of hf hx, chargesUse_of hf hx]
  cases h'.storage key <;> simp [chargesUse_of hf hx]

theorem storageWriteHost_erase {h h' : NearState} (he : erase h = erase h') (extra : Nat) (key val : List UInt8)
    (r : UInt64) (s2 : State) : erase (storageWriteHost extra h key val r s2) = erase (storageWriteHost extra h' key val r s2) := by
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  have hu : h.context.storageUsage = h'.context.storageUsage :=
    erase_field he (fun x : NearState => x.context.storageUsage) fun _ => rfl
  have hw : erase { h with storageAccounting := some s2 } = erase { h' with storageAccounting := some s2 } := by
    show { erase h with storageAccounting := some s2 } = { erase h' with storageAccounting := some s2 }
    rw [he]
  unfold storageWriteHost
  rw [erase_logWrite, erase_logWrite, erase_setStorage_inv, erase_setStorage_inv, erase_storageReadRegs,
    erase_storageReadRegs, hw, hs, hu]

theorem storageWritePost_erase {h h' host' : NearState} (he : erase h = erase h') {extra : Nat}
    {key val : List UInt8} {r : UInt64} {s : State} (hq : StorageWritePost extra h key val r s host') :
    StorageWritePost extra h' key val r s host' := by
  obtain ⟨s1, hsd, hre, hq⟩ := hq
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  have hi : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  refine ⟨s1, hsd, ?_, ?_⟩
  · rw [← hs, ← hi]; exact hre
  · rw [hq, ← hi, storageWriteHost_erase he]

/-- **`storage_write`, metered**, as a two-range read contract: with the key's `kl` bytes `key`
at `kp` and the value's `vl` bytes `val` at `vp`, over a host whose storage accounting `s` is a
canonical trie linked to its `storage` (`hlink`), and not a view call, the call returns `1` (and
sets register `r` to the old value) or `0`, leaves the host as `StorageWritePost`, and uses at
most `storageWriteUse` gas. -/
theorem storageWrite_readContract (extra : Nat) (h : NearState) (kl kp vl vp r : UInt64) (key val : List UInt8)
    (s : State) {C b : Nat} (hkl : kl ≠ u64Max) (hvl : vl ≠ u64Max)
    (hkn : key.length = kl.toNat) (hvn : val.length = vl.toNat) (hkpos : 0 < kl.toNat) (hvpos : 0 < vl.toNat)
    (hview : h.context.isView = false)
    (hacc : h.storageAccounting = some s)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hvlim : withinLimit h.config.maxStorageValueLen val.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal s (contractKey h.context.currentAccountId key))
    (hproof : ProofBudget h s b)
    (hbud : writeProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ b)
    (hreg : ∀ v, h.storage key = some v → r ≠ u64Max → withinLimit h.config.maxRegisterLen v.length = true) :
    ReadContractP2 (metered extra "storage_write" storageWriteFn).toHostFn h (StorageWritePost extra h key val r s)
      [.i64 kl, .i64 kp, .i64 vl, .i64 vp, .i64 r] (storageReadResult (h.storage key)) kp.toNat key vp.toNat val
      (storageWriteUse h key kl.toNat vl.toNat) C := by
  intro host mem hwf he hrd1 hrd2 hu hmb hpp
  have fsa : host.storageAccounting = h.storageAccounting := erase_field he NearState.storageAccounting fun _ => rfl
  have fid : host.context.currentAccountId = h.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have fview : host.context.isView = h.context.isView :=
    erase_field he (fun x : NearState => x.context.isView) fun _ => rfl
  have fcfg : host.config = h.config := erase_field he NearState.config fun _ => rfl
  have fsto : host.storage = h.storage := erase_field he NearState.storage fun _ => rfl
  have fpsz : host.storageProofSize = h.storageProofSize := erase_field he NearState.storageProofSize fun _ => rfl
  have hin : ∀ (ptr len : UInt64) (bs : List UInt8), bs.length = len.toNat → 0 < len.toNat → len ≠ u64Max →
      (∀ k, k < bs.length → ptr.toNat + k < mem.byteSize ∧ mem.read8 (ptr.toNat + k) = bs[k]!) →
      getMemOrReg { mem, host } ptr len = some bs := by
    intro ptr len bs hbl hpos hne hrd
    have hin : ptr.toNat + len.toNat ≤ mem.size * 65536 := by
      have := (hrd (len.toNat - 1) (by omega)).1
      unfold Memory.byteSize at this
      show _ ≤ mem.pages.size * 65536
      unfold pageSize at this
      omega
    simp only [getMemOrReg, hne, ite_false]
    rw [if_neg (by show ¬ _ > mem.pages.size * 65536; show ¬ _ > mem.size * 65536; omega)]
    rw [← hbl]
    exact congrArg some (readList_eq fun k hk => (hrd k hk).2)
  have hkey := hin kp kl key hkn hkpos hkl hrd1
  have hval := hin vp vl val hvn hvpos hvl hrd2
  rw [← storageWriteUse_erase he] at hu ⊢
  obtain ⟨host', hinv, hq, hused, hmb', hpp'⟩ := storageWrite_ok extra { mem, host } kl kp vl vp r key val s (C := C)
    hkl hvl (by rw [← hview]; exact fview) hkey hval hkn hvn (by rw [fsa]; exact hacc) (by rw [fcfg]; exact hlim)
    (by rw [fcfg]; exact hvlim) hb hz (by rw [fsto, fid]; exact hlink) (hproof.congr fpsz fcfg)
    (by rw [fid, fsto]; exact hbud) (by rw [fsto, fcfg]; exact hreg) hu hmb hpp
  refine ⟨host', ?_, storageWritePost_erase he hq, hused, hmb', hpp'⟩
  simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
  rw [show host.storage key = h.storage key by rw [fsto]]

/-! ## The overlay after a write -/

theorem viewVal_sameData {s s' : State} (h : SameData s s') (k : List UInt8) : viewVal s' k = viewVal s k := by
  obtain ⟨h1, -, h3, h4⟩ := h
  unfold viewVal
  rw [h1, h3, h4]

open private insert from NearInterface.TrieOverlay in
theorem set_prospective (s : State) (k v : List UInt8) :
    (s.set k v).prospective = (k, some v) :: s.prospective.filter (·.1 != k) := rfl

theorem viewVal_set_same (s : State) (k v : List UInt8) : viewVal (s.set k v) k = some v := by
  simp [viewVal, set_prospective]

theorem viewVal_set_other (s : State) {k k' : List UInt8} (v : List UInt8) (hk : k' ≠ k) :
    viewVal (s.set k v) k' = viewVal s k' := by
  have hf : (s.set k v).prospective.find? (·.1 == k') = s.prospective.find? (·.1 == k') := by
    rw [set_prospective, List.find?_cons_of_neg (by simpa using Ne.symm hk)]
    rw [List.find?_filter]
    congr 1
    funext a
    by_cases ha : a.1 = k'
    · subst ha; simp [hk]
    · simp [ha]
  unfold viewVal
  rw [hf]
  rfl

theorem contractKey_inj {a k1 k2 : List UInt8} (h : contractKey a k1 = contractKey a k2) : k1 = k2 := by
  unfold contractKey at h
  exact List.append_cancel_left h

/-- The host's contract storage is the overlay's view of the account's keys. -/
def StorageLink (h : NearState) (s : State) : Prop :=
  ∀ k, h.storage k = viewVal s (contractKey h.context.currentAccountId k)

/-- The overlay's base is the canonical trie of its entries, with no object hashing to zero. -/
def Canon (s : State) : Prop := build s.entries = .ok s.base ∧ zeroHash ∉ s.base.witness.map Prod.fst

theorem Canon.sameData {s s' : State} (hc : Canon s) (h : SameData s s') : Canon s' := by
  obtain ⟨h1, h2, -, -⟩ := h
  unfold Canon
  rw [h1, h2]
  exact hc

theorem Canon.set {s : State} (hc : Canon s) (k v : List UInt8) : Canon (s.set k v) := hc

theorem StorageLink.sameData {h : NearState} {s s' : State} (hl : StorageLink h s) (hsd : SameData s s') :
    StorageLink h s' := fun k => (hl k).trans (viewVal_sameData hsd _).symm

theorem StorageLink.erase {h h' : NearState} {s : State} (hl : StorageLink h s) (he : erase h' = erase h) :
    StorageLink h' s := by
  have hs : h'.storage = h.storage := erase_field he NearState.storage fun _ => rfl
  have hi : h'.context.currentAccountId = h.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  intro k; rw [hs, hi]; exact hl k

theorem storageWriteHost_storage (extra : Nat) (h : NearState) (key val : List UInt8) (r : UInt64) (s2 : State) :
    (storageWriteHost extra h key val r s2).storage = fun k => if k = key then some val else h.storage k := by
  unfold storageWriteHost logWrite
  simp only [NearState.invalidateIterators, NearState.setStorage]
  unfold storageReadRegs
  split
  · split <;> rfl
  · rfl

theorem storageWriteHost_context_id (extra : Nat) (h : NearState) (key val : List UInt8) (r : UInt64)
    (s2 : State) : (storageWriteHost extra h key val r s2).context.currentAccountId = h.context.currentAccountId := by
  unfold storageWriteHost logWrite
  simp only [NearState.invalidateIterators, NearState.setStorage]
  rw [storageReadRegs_context]

/-- A write keeps the host linked to the overlay. -/
theorem StorageLink.write {h : NearState} {s s1 : State} (hl : StorageLink h s) (hsd : SameData s s1)
    (extra : Nat) (key val : List UInt8) (r : UInt64) :
    StorageLink (storageWriteHost extra h key val r (s1.set (contractKey h.context.currentAccountId key) val))
      (s1.set (contractKey h.context.currentAccountId key) val) := by
  intro k
  rw [storageWriteHost_storage, storageWriteHost_context_id]
  by_cases hk : k = key
  · subst hk; simp [viewVal_set_same]
  · simp only [hk, ite_false]
    rw [viewVal_set_other _ _ (fun he => hk (contractKey_inj he)), viewVal_sameData hsd]
    exact hl k

/-- What `storage_write` leaves meets the hypotheses of the next storage call: the accounting is a
canonical trie linked to the storage, with the budget spent. -/
theorem StorageWritePost.next {extra : Nat} {h host' : NearState} {key val : List UInt8} {r : UInt64}
    {s : State} {b : Nat} (hq : StorageWritePost extra h key val r s host') (hc : Canon s) (hl : StorageLink h s)
    (hproof : ProofBudget h s b) (hbud : writeProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ b) :
    ∃ s2, host'.storageAccounting = some s2 ∧ Canon s2 ∧ StorageLink host' s2 ∧
      ProofBudget host' s2 (b - writeProofCost (contractKey h.context.currentAccountId key) (h.storage key)) ∧
      erase host' = erase (storageWriteHost extra h key val r s2) := by
  obtain ⟨s1, hsd, hre, he⟩ := hq
  refine ⟨_, ?_, (hc.sameData hsd).set _ _, (hl.write hsd extra key val r).erase he, ?_, he⟩
  · rw [erase_field he NearState.storageAccounting fun _ => rfl]
    unfold storageWriteHost logWrite
    simp only [NearState.invalidateIterators, NearState.setStorage]
    unfold storageReadRegs
    split
    · split <;> rfl
    · rfl
  · have hpb := hproof.reach hre hbud
    refine hpb.congr ?_ ?_
    · rw [erase_field he NearState.storageProofSize fun _ => rfl]
      unfold storageWriteHost logWrite
      simp only [NearState.invalidateIterators, NearState.setStorage]
      unfold storageReadRegs
      split
      · split <;> rfl
      · rfl
    · rw [erase_field he NearState.config fun _ => rfl]
      unfold storageWriteHost logWrite
      simp only [NearState.invalidateIterators, NearState.setStorage]
      unfold storageReadRegs
      split
      · split <;> rfl
      · rfl


/-- `storage_read`'s register update keeps every field `setRegister` keeps. -/
theorem storageReadRegs_field {α : Type} (f : NearState → α) (hf : ∀ x i v, f (x.setRegister i v) = f x)
    (x : NearState) (r : UInt64) (val : Option (List UInt8)) : f (storageReadRegs x r val) = f x := by
  unfold storageReadRegs
  split
  · split
    · rfl
    · exact hf _ _ _
  · rfl

/-- What `storage_read` leaves meets the hypotheses of the next storage call: the accounting is a
canonical trie linked to the storage, with the budget spent by the lookup and the dereference
(`readProofCost`). -/
theorem StorageReadPost.next {h host' : NearState} {key : List UInt8} {r : UInt64} {s : State} {b : Nat}
    (hq : StorageReadPost h key r s host') (hc : Canon s) (hl : StorageLink h s) (hproof : ProofBudget h s b)
    (hbud : readProofCost (contractKey h.context.currentAccountId key) (h.storage key) ≤ b) :
    ∃ s2, host'.storageAccounting = some s2 ∧ Canon s2 ∧ StorageLink host' s2 ∧
      ProofBudget host' s2 (b - readProofCost (contractKey h.context.currentAccountId key) (h.storage key)) ∧
      erase host' = erase (storageReadRegs { h with storageAccounting := some s2 } r (h.storage key)) := by
  obtain ⟨s2, hsd, hre, he⟩ := hq
  have hfield : ∀ {α : Type} (f : NearState → α), (∀ x, f (erase x) = f x) →
      (∀ x i v, f (x.setRegister i v) = f x) →
      f host' = f { h with storageAccounting := some s2 } := fun f hfe hfr =>
    (erase_field he f hfe).trans (storageReadRegs_field f hfr _ _ _)
  refine ⟨s2, hfield NearState.storageAccounting (fun _ => rfl) (fun _ _ _ => rfl), hc.sameData hsd, ?_, ?_, he⟩
  · intro k
    rw [hfield NearState.storage (fun _ => rfl) (fun _ _ _ => rfl),
      hfield (fun x => x.context.currentAccountId) (fun _ => rfl) (fun _ _ _ => rfl)]
    exact (hl.sameData hsd) k
  · exact (hproof.reach hre hbud).congr (hfield NearState.storageProofSize (fun _ => rfl) (fun _ _ _ => rfl))
      (hfield NearState.config (fun _ => rfl) (fun _ _ _ => rfl))

end NearLogic
