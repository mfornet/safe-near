import NearLogic.Hosts.StorageWrite

/-!
# `storage_has_key`, metered

The host contract of metered `storage_has_key(key_len, key_ptr)` with the key in memory, over a
host whose storage accounting is a canonical overlay linked to its `storage` (`viewVal`), as
`storage_read` (`StorageRead.lean`) but with no value read.

* `prepareStorageCallAux_hasKey`: the storage phase succeeds; it only moves the trie's
  accounting (`SameData`), records at most the lookup (`ProofReach`, `lookupProofBound`) and burns
  at most `readNodes` nodes at the dearer node cost (none at the boundary).
* `storageHasKey_readContract`: the whole metered call as a `ReadContractP`: returns `1` when the
  key has a value, `0` otherwise (`storageReadResult`); the host is unchanged up to gas and the
  accounting's caches (`StorageHasKeyPost`); the gas is at most `storageHasKeyUse`.
-/

namespace NearLogic

open Wasm Wasm.Near Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

theorem prepareStorageCallAux_hasKey (before : HostStore NearState) (len ptr : UInt64)
    (key rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before ptr len = some key)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : lookupProofBound rawKey ≤ b)
    (h1 : before.host.gas.used + readNodes before.host rawKey * trieNodeMax before.host ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ after s', prepareStorageCallAux "storage_has_key" before [.i64 len, .i64 ptr] = (after, none) ∧
      after.host.storageAccounting = some s' ∧ SameData s s' ∧ ProofReach s s' (lookupProofBound rawKey) ∧
      after.host.gas.burnt ≤ before.host.gas.burnt + readNodes before.host rawKey * trieNodeMax before.host ∧
      after.host.gas.promises = before.host.gas.promises := by
  obtain ⟨s', p, hget, hsd, ⟨d, m, hd, hm, hdm⟩, hpres, -⟩ :=
    storage_lookup_view (k := rawKey) before.host.storageReadsFromTrie hb hz
  have hcon : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "storage_has_key" = true := by decide
  have e1 : ("storage_has_key" == "storage_write") = false := by decide
  have e2 : ("storage_has_key" == "storage_remove") = false := by decide
  have e3 : ("storage_has_key" != "storage_has_key") = false := by decide
  have hlk : ∀ l, before.host.config.maxStorageKeyLen = some l → ¬ key.length > l := by
    intro l hl; rw [hl] at hlim; simpa [withinLimit] using hlim
  have hdd : s'.accounting.disk - s.accounting.disk = d := by omega
  have hmm : s'.accounting.mem - s.accounting.mem = m := by omega
  rw [← hlink] at hpres
  have hpres' : (p.isSome != (before.host.storage key).isSome) = false := by
    rw [hpres]; exact bne_self_eq_false _
  simp only [prepareStorageCallAux, hcon, hacc, argU64, Id.run]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, hkey, e1, e2, e3, Bool.false_or,
    ite_true, Bool.false_eq_true, ite_false]
  rw [← hraw, hget]
  split
  on_goal 1 => rename_i lim hml; rw [if_neg (hlk lim hml)]
  all_goals
    dsimp only
    rw [hpres']
    simp only [Bool.false_eq_true, ite_false]
    rw [hdd, hmm]
    set ns0 : NearState := { before.host with storageAccounting := some s' } with hns0
    have hu0 : ns0.gas = before.host.gas := rfl
    have htc : chargesUse ns0 (trieNodeCharges d m) ≤ readNodes before.host rawKey * trieNodeMax before.host :=
      Nat.le_trans (trieNodeCharges_use ns0 d m) (Nat.mul_le_mul_right _ (lookup_readNodes hget hd hm hdm))
    obtain ⟨ns1, hA, ch1, pr1⟩ := bill_ext ns0 (trieNodeCharges d m) (extOnly_trie d m) (C := C)
      (by rw [hu0]; omega) h2 h3
    simp only [trieNodeCharges] at hA
    rw [hA]
    have hreach : ProofReach s s' (lookupProofBound rawKey) := by
      have := ProofReach.step (ProofStep.lookup hget) (ProofReach.refl _)
      simpa using this
    have hpsz : ns1.storageProofSize = before.host.storageProofSize :=
      erase_field ch1.erase NearState.storageProofSize fun _ => rfl
    have hrec : recordedStorageError ns1 s' = none :=
      recordedStorageError_reach (hproof.congr hpsz ch1.config) hreach hbud
    simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false, hrec]
    have hsa1 : ns1.storageAccounting = some s' := erase_field ch1.erase NearState.storageAccounting fun _ => rfl
    refine ⟨_, s', rfl, hsa1, hsd, hreach, ?_, pr1⟩
    have hu1 := ch1.used
    have q1 := pr1
    rw [hu0] at q1
    simp only [Near.GasCounter.used] at hu1 h1
    rw [hu0] at hu1
    show ns1.gas.burnt ≤ _
    omega

/-- The host after the storage phase of `storage_has_key`. -/
theorem prepareStorageCall_hasKey (before : HostStore NearState) (len ptr : UInt64)
    (key rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before ptr len = some key)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : lookupProofBound rawKey ≤ b)
    (h1 : before.host.gas.used + readNodes before.host rawKey * trieNodeMax before.host ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ s2 bt p, prepareStorageCall "storage_has_key" before [.i64 len, .i64 ptr] =
        ({ before with host := phaseHost before.host s2 bt p }, none) ∧ SameData s s2 ∧
      ProofReach s s2 (lookupProofBound rawKey) ∧
      bt ≤ before.host.gas.burnt + readNodes before.host rawKey * trieNodeMax before.host := by
  obtain ⟨after, s2, haux, hsa, hsd, hre, hb', -⟩ :=
    prepareStorageCallAux_hasKey before len ptr key rawKey s hraw hacc hkey hlim hb hz hlink hproof hbud h1 h2 h3
  refine ⟨s2, after.host.gas.burnt, after.host.gasProfile, ?_, hsd, hre, hb'⟩
  simp only [prepareStorageCall, haux, hsa, Option.isNone_none, ite_true, phaseHost]

/-! ## The metered call -/

/-- The charges of `storage_has_key` before it runs, for a key of `n` bytes in memory. -/
def storageHasKeyBeforeCharges (n : Nat) : List Charge :=
  [.ext "base", .ext "storage_has_key_base", .ext "read_memory_base", .ext "read_memory_byte" n,
    .ext "storage_has_key_byte" n]

theorem chargesBefore_storageHasKey (st : HostStore NearState) (len ptr : UInt64) (hlen : len ≠ u64Max) :
    chargesBefore "storage_has_key" st [.i64 len, .i64 ptr] = storageHasKeyBeforeCharges len.toNat := by
  have hs : storageMutationPlan? "storage_has_key" st [.i64 len, .i64 ptr] = none := by
    simp [storageMutationPlan?]
  have hpre : "storage_has_key".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, readSpan, spanLen,
    hlen, storageHasKeyBeforeCharges]

theorem preInvokeError_storageHasKey (st : HostStore NearState) (args : List Value) :
    preInvokeError "storage_has_key" st args = none := by
  simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
    creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
    functionCallInputError, functionCallInputs?]

/-- Post-call metering of `storage_has_key`: nothing. -/
theorem finish_storageHasKey (extra : Nat) (before st : HostStore NearState) (args vals : List Value) :
    finishMeteredCall extra "storage_has_key" before args (.Return vals st) = .Return vals st := by
  simp (config := { decide := true }) [finishMeteredCall, chargesAfter, applyCharges, deductDeposit,
    promiseDeposit?, actionMethodEncodingError, actionMethodBytes?, functionCallInputs?, updateStorageUsage]

theorem storageHasKeyFn_invoke (st : HostStore NearState) (len ptr : UInt64) (key : List UInt8)
    (hkey : getMemOrReg st ptr len = some key)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true) :
    storageHasKeyFn.invoke st [.i64 len, .i64 ptr] = .Return (storageReadResult (st.host.storage key)) st := by
  simp only [storageHasKeyFn, hkey, checkDataLimit, hlim, ite_true]
  cases st.host.storage key <;> rfl

/-- What `storage_has_key(key)` leaves of `h`, up to gas: the accounting replaced by one with the
data of `s`, reached by the lookup. -/
def StorageHasKeyPost (h : NearState) (key : List UInt8) (s : State) (host' : NearState) : Prop :=
  ∃ s2, SameData s s2 ∧ ProofReach s s2 (lookupProofBound (contractKey h.context.currentAccountId key)) ∧
    erase host' = erase { h with storageAccounting := some s2 }

/-- The gas `storage_has_key` of an `n`-byte key may use. -/
def storageHasKeyUse (h : NearState) (key : List UInt8) (n : Nat) : Nat :=
  chargesUse h (storageHasKeyBeforeCharges n) +
    readNodes h (contractKey h.context.currentAccountId key) * trieNodeMax h

theorem storageHasKey_ok (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) (key : List UInt8)
    (s : State) {C b : Nat} (hlen : len ≠ u64Max)
    (hkey : getMemOrReg st ptr len = some key)
    (hacc : st.host.storageAccounting = some s)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : st.host.storage key = viewVal s (contractKey st.host.context.currentAccountId key))
    (hproof : ProofBudget st.host s b)
    (hbud : lookupProofBound (contractKey st.host.context.currentAccountId key) ≤ b)
    (h1 : st.host.gas.used + storageHasKeyUse st.host key len.toNat ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "storage_has_key" storageHasKeyFn).invoke st [.i64 len, .i64 ptr] =
        .Return (storageReadResult (st.host.storage key)) { mem := st.mem, host := host' } ∧
      StorageHasKeyPost st.host key s host' ∧
      host'.gas.used ≤ st.host.gas.used + storageHasKeyUse st.host key len.toNat ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  have hdep : deprecatedRuntimeHost "storage_has_key" = false := by decide
  have hview : viewRestrictedHost "storage_has_key" = false := by decide
  have hu := h1
  unfold storageHasKeyUse at hu
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (storageHasKeyBeforeCharges len.toNat) (C := C) (by omega) h2 h3
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [chargesBefore_storageHasKey st len ptr hlen]
  generalize hac : applyCharges st.host (storageHasKeyBeforeCharges len.toNat) = ac at hok hch
  obtain ⟨ns, err⟩ := ac
  simp only at hok hch
  subst hok
  simp only
  rw [preInvokeError_storageHasKey]
  simp only
  show ∃ host', invokeStorageCall extra "storage_has_key" storageHasKeyFn
    { mem := st.mem, host := afterCharges ns } [.i64 len, .i64 ptr] = _ ∧ _
  have he1 : erase (afterCharges ns) = erase st.host := by rw [erase_afterCharges, hch.erase]
  have fsa : (afterCharges ns).storageAccounting = st.host.storageAccounting :=
    erase_field he1 NearState.storageAccounting fun _ => rfl
  have fid : (afterCharges ns).context.currentAccountId = st.host.context.currentAccountId :=
    erase_field he1 (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have fcfg : (afterCharges ns).config = st.host.config := erase_field he1 NearState.config fun _ => rfl
  have fsto : (afterCharges ns).storage = st.host.storage := erase_field he1 NearState.storage fun _ => rfl
  have fpsz : (afterCharges ns).storageProofSize = st.host.storageProofSize :=
    erase_field he1 NearState.storageProofSize fun _ => rfl
  have fext : (afterCharges ns).extCosts = st.host.extCosts := erase_field he1 NearState.extCosts fun _ => rfl
  have hgas1 : (afterCharges ns).gas = ns.gas := rfl
  have hkey1 : getMemOrReg { mem := st.mem, host := afterCharges ns } ptr len = some key :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := afterCharges ns }) hlen rfl).trans hkey
  have hmx : trieNodeMax (afterCharges ns) = trieNodeMax st.host := by simp only [trieNodeMax, fext]
  have hrn : readNodes (afterCharges ns) = readNodes st.host := by
    have : (afterCharges ns).storageReadsFromTrie = st.host.storageReadsFromTrie :=
      erase_field he1 NearState.storageReadsFromTrie fun _ => rfl
    funext k; simp only [readNodes, this]
  obtain ⟨s2, bt, p, hpre, hsd, hre, hbb⟩ := prepareStorageCall_hasKey { mem := st.mem, host := afterCharges ns }
    len ptr key (contractKey st.host.context.currentAccountId key) s (C := C) (by rw [fid])
    (by rw [fsa]; exact hacc) hkey1 (by rw [fcfg]; exact hlim) hb hz
    (by rw [fsto]; exact hlink) (hproof.congr fpsz fcfg) hbud
    (by rw [hmx, hrn, hgas1, hch.used]; omega) (by rw [hgas1, hch.maxBurnt]; exact h2)
    (by rw [hgas1, hch.prepaid]; exact h3)
  rw [hmx, hrn] at hbb
  have hbb' : bt ≤ ns.gas.burnt + readNodes st.host (contractKey st.host.context.currentAccountId key) *
      trieNodeMax st.host := hbb
  simp only [invokeStorageCall, hpre]
  set H2 := phaseHost (afterCharges ns) s2 bt p with hH2
  have hkey2 : getMemOrReg { mem := st.mem, host := H2 } ptr len = some key :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := H2 }) hlen rfl).trans hkey
  have hsto2 : H2.storage = st.host.storage := fsto
  have hcfg2 : H2.config = st.host.config := fcfg
  rw [storageHasKeyFn_invoke { mem := st.mem, host := H2 } len ptr key hkey2 (by rw [hcfg2]; exact hlim),
    finish_storageHasKey, hsto2]
  have hn := hch.used
  simp only [Near.GasCounter.used] at hn hu
  refine ⟨H2, rfl, ⟨s2, hsd, hre, ?_⟩, ?_, ?_, ?_⟩
  · show { erase (afterCharges ns) with storageAccounting := some s2 } = _
    rw [he1]; rfl
  · show bt + ns.gas.promises ≤ _
    unfold storageHasKeyUse
    simp only [Near.GasCounter.used]
    omega
  · exact hch.maxBurnt
  · exact hch.prepaid

theorem storageHasKeyUse_erase {h h' : NearState} (he : erase h = erase h') (key : List UInt8) (n : Nat) :
    storageHasKeyUse h key n = storageHasKeyUse h' key n := by
  have hf : h.fees = h'.fees := erase_field he NearState.fees fun _ => rfl
  have hx : h.extCosts = h'.extCosts := erase_field he NearState.extCosts fun _ => rfl
  have hi : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have hrt : h.storageReadsFromTrie = h'.storageReadsFromTrie :=
    erase_field he NearState.storageReadsFromTrie fun _ => rfl
  unfold storageHasKeyUse trieNodeMax readNodes
  rw [hi, hx, hrt, chargesUse_of hf hx]

theorem storageHasKeyPost_erase {h h' host' : NearState} (he : erase h = erase h') {key : List UInt8}
    {s : State} (hq : StorageHasKeyPost h key s host') : StorageHasKeyPost h' key s host' := by
  obtain ⟨s2, hsd, hre, hq⟩ := hq
  have hi : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  refine ⟨s2, hsd, by rw [← hi]; exact hre, ?_⟩
  rw [hq]
  show { erase h with storageAccounting := some s2 } = { erase h' with storageAccounting := some s2 }
  rw [he]

/-- **`storage_has_key`, metered**, as a read contract. -/
theorem storageHasKey_readContract (extra : Nat) (h : NearState) (len ptr : UInt64) (key : List UInt8)
    (s : State) {C b : Nat} (hlen : len ≠ u64Max) (hkl : key.length = len.toNat) (hpos : 0 < len.toNat)
    (hacc : h.storageAccounting = some s)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal s (contractKey h.context.currentAccountId key))
    (hproof : ProofBudget h s b) (hbud : lookupProofBound (contractKey h.context.currentAccountId key) ≤ b) :
    ReadContractP (metered extra "storage_has_key" storageHasKeyFn).toHostFn h (StorageHasKeyPost h key s)
      [.i64 len, .i64 ptr] (storageReadResult (h.storage key)) ptr.toNat key
      (storageHasKeyUse h key len.toNat) C := by
  intro host mem hwf he hrd hu hmb hpp
  have fsa : host.storageAccounting = h.storageAccounting := erase_field he NearState.storageAccounting fun _ => rfl
  have fid : host.context.currentAccountId = h.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have fcfg : host.config = h.config := erase_field he NearState.config fun _ => rfl
  have fsto : host.storage = h.storage := erase_field he NearState.storage fun _ => rfl
  have fpsz : host.storageProofSize = h.storageProofSize := erase_field he NearState.storageProofSize fun _ => rfl
  have hin : ptr.toNat + len.toNat ≤ mem.size * 65536 := by
    have := (hrd (len.toNat - 1) (by omega)).1
    unfold Memory.byteSize at this
    show _ ≤ mem.pages.size * 65536
    unfold pageSize at this
    omega
  have hkey : getMemOrReg { mem, host } ptr len = some key := by
    simp only [getMemOrReg, hlen, ite_false]
    rw [if_neg (by show ¬ _ > mem.pages.size * 65536; show ¬ _ > mem.size * 65536; omega)]
    rw [← hkl]
    exact congrArg some (readList_eq fun k hk => (hrd k hk).2)
  rw [← storageHasKeyUse_erase he] at hu ⊢
  obtain ⟨host', hinv, hq, hused, hmb', hpp'⟩ := storageHasKey_ok extra { mem, host } len ptr key s (C := C)
    hlen hkey (by rw [fsa]; exact hacc) (by rw [fcfg]; exact hlim) hb hz
    (by rw [fsto, fid]; exact hlink) (hproof.congr fpsz fcfg) (by rw [fid]; exact hbud) hu hmb hpp
  refine ⟨host', ?_, storageHasKeyPost_erase he hq, hused, hmb', hpp'⟩
  simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
  rw [show host.storage key = h.storage key by rw [fsto]]

/-- What `storage_has_key` leaves meets the hypotheses of the next storage call. -/
theorem StorageHasKeyPost.next {h host' : NearState} {key : List UInt8} {s : State} {b : Nat}
    (hq : StorageHasKeyPost h key s host') (hc : Canon s) (hl : StorageLink h s) (hproof : ProofBudget h s b)
    (hbud : lookupProofBound (contractKey h.context.currentAccountId key) ≤ b) :
    ∃ s2, host'.storageAccounting = some s2 ∧ Canon s2 ∧ StorageLink host' s2 ∧
      ProofBudget host' s2 (b - lookupProofBound (contractKey h.context.currentAccountId key)) ∧
      erase host' = erase { h with storageAccounting := some s2 } := by
  obtain ⟨s2, hsd, hre, he⟩ := hq
  refine ⟨s2, erase_field he NearState.storageAccounting fun _ => rfl, hc.sameData hsd,
    (show StorageLink { h with storageAccounting := some s2 } s2 from hl.sameData hsd).erase he, ?_, he⟩
  exact (hproof.reach hre hbud).congr (erase_field he NearState.storageProofSize fun _ => rfl)
    (erase_field he NearState.config fun _ => rfl)

end NearLogic
