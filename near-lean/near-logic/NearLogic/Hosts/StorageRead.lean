import NearLogic.Hosts.Registers
import NearLogic.Trie
import NearInterface.StorageProof
import NearLogic.CallPred

/-!
# `storage_read`, metered

The host contract of metered `storage_read(key_len, key_ptr, register_id)`
with the key in memory, over a host whose storage accounting is an overlay on a
canonical trie, linked to the host's `storage` through the overlay's view
(`viewVal`): a pending change is read from the overlay, any other key from the
trie (`storage_lookup_view`).

* `prepareStorageCall_read`: the external storage phase succeeds; it only
  moves the trie's accounting (`SameData`) and burns at most
  `storageReadPhaseUse`: the lookup's `2·|rawKey| + 1` nodes at the dearer of
  the two node costs, and the value-byte charges when the key is present.
* `storageRead_readContract`: the whole metered call as a `ReadContractP`:
  returns `[.i64 1]` and sets the register to the value when present,
  `[.i64 0]` when absent; the resulting host is described by
  `StorageReadPost`; the gas is at most `storageReadUse`.
-/

namespace NearLogic

open Wasm Wasm.Near Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-! ## Charges -/

/-- Every charge is an `ext` charge (burnt, no promise gas). -/
def ExtOnly (cs : List Charge) : Prop := ∀ c ∈ cs, ∃ n t, c = .ext n t

theorem applyCharge_ext_promises (ns : NearState) (n : String) (t : Nat) {C : Nat}
    (h1 : ns.gas.used + chargeUse ns (.ext n t) ≤ C) (h2 : C ≤ ns.gas.maxBurnt) (h3 : C ≤ ns.gas.prepaid) :
    (applyCharge ns (.ext n t)).1.gas.promises = ns.gas.promises := by
  simp only [chargeUse] at h1
  simp [applyCharge, Near.GasCounter.burn, deduct_ok (Nat.le_refl _) h1 h2 h3]

/-- `ext` charges within the credits leave the promise gas alone. -/
theorem applyCharges_ext_promises (ns : NearState) (cs : List Charge) (hx : ExtOnly cs) {C : Nat}
    (h1 : ns.gas.used + chargesUse ns cs ≤ C) (h2 : C ≤ ns.gas.maxBurnt) (h3 : C ≤ ns.gas.prepaid) :
    (applyCharges ns cs).1.gas.promises = ns.gas.promises := by
  induction cs generalizing ns with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨n, t, rfl⟩ := hx _ List.mem_cons_self
    simp only [chargesUse, List.map_cons, List.sum_cons] at h1
    obtain ⟨he, hc⟩ := applyCharge_ok ns (.ext n t) (C := C) (by omega) h2 h3
    have hp := applyCharge_ext_promises ns n t (C := C) (by omega) h2 h3
    have hcs : chargesUse (applyCharge ns (.ext n t)).1 cs = chargesUse ns cs := by
      unfold chargesUse
      congr 1
      first | done | exact List.map_congr_left fun c _ => chargeUse_congr hc.fees hc.extCosts c
    have := ih (applyCharge ns (.ext n t)).1 (fun c hc => hx c (List.mem_cons_of_mem _ hc))
      (by rw [hcs, hc.used]; simp only [chargesUse] at h1 ⊢; omega)
      (by rw [hc.maxBurnt]; exact h2) (by rw [hc.prepaid]; exact h3)
    simp only [applyCharges]
    rw [show applyCharge ns (.ext n t) = ((applyCharge ns (.ext n t)).1, none) by rw [← he]]
    simp only
    rw [this, hp]

theorem chargesUse_of {ns ns' : NearState} (hf : ns'.fees = ns.fees) (he : ns'.extCosts = ns.extCosts)
    (cs : List Charge) : chargesUse ns' cs = chargesUse ns cs := by
  unfold chargesUse
  congr 1
  exact List.map_congr_left fun c _ => chargeUse_congr hf he c

/-- The charges of the trie lookup: nodes read from disk, and from the cache. -/
def trieNodeCharges (d m : Nat) : List Charge :=
  [.ext "touching_trie_node" d, .ext "read_cached_trie_node" m]

/-- The dearer of the two trie node costs. -/
def trieNodeMax (h : NearState) : Nat :=
  max (h.extCosts.cost "touching_trie_node") (h.extCosts.cost "read_cached_trie_node")

theorem trieNodeCharges_use (h : NearState) (d m : Nat) :
    chargesUse h (trieNodeCharges d m) ≤ (d + m) * trieNodeMax h := by
  simp only [chargesUse, trieNodeCharges, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    chargeUse, trieNodeMax, Nat.add_mul]
  have a := Nat.le_max_left (h.extCosts.cost "touching_trie_node") (h.extCosts.cost "read_cached_trie_node")
  have b := Nat.le_max_right (h.extCosts.cost "touching_trie_node") (h.extCosts.cost "read_cached_trie_node")
  have := Nat.mul_le_mul_right d a
  have := Nat.mul_le_mul_right m b
  have e1 := Nat.mul_comm d (max (h.extCosts.cost "touching_trie_node") (h.extCosts.cost "read_cached_trie_node"))
  have e2 := Nat.mul_comm m (max (h.extCosts.cost "touching_trie_node") (h.extCosts.cost "read_cached_trie_node"))
  omega

/-- The gas the storage phase of `storage_read` may burn, for the raw trie key
`rawKey` and the value `val` found: the lookup's nodes, then the value bytes. -/
def storageReadPhaseUse (h : NearState) (rawKey : List UInt8) (val : Option (List UInt8)) : Nat :=
  (2 * rawKey.length + 1) * trieNodeMax h +
    ((val.map fun v => chargesUse h (storageReadValueCharges v.length)).getD 0)

/-- The recorded proof has room for `b` more bytes from the overlay `s` (SAF-67):
every overlay the VM's operations reach from `s` while recording at most `b`
bytes keeps the proof within the limit. `Context.WF.proof_growth` and
`Context.ProofRoom` give it for the context's trie. -/
def ProofBudget (h : NearState) (s : State) (b : Nat) : Prop :=
  ∀ size, h.storageProofSize = some size → ∀ t c, ProofReach s t c → c ≤ b →
    size t ≤ h.config.maxStorageProofSize

theorem ProofBudget.congr {h h' : NearState} {s : State} {b : Nat} (hp : ProofBudget h s b)
    (hs : h'.storageProofSize = h.storageProofSize) (hc : h'.config = h.config) : ProofBudget h' s b := by
  intro size hsz t c hr hcb
  rw [hc]
  rw [hs] at hsz
  exact hp size hsz t c hr hcb

/-- One operation spends its share of the budget. -/
theorem ProofBudget.step {h : NearState} {s t : State} {a b : Nat} (hp : ProofBudget h s b)
    (hst : ProofStep s t a) (hab : a ≤ b) : ProofBudget h t (b - a) := by
  intro size hsz u c hr hcb
  exact hp size hsz u (a + c) (.step hst hr) (by omega)

theorem ProofBudget.mono {h : NearState} {s : State} {a b : Nat} (hp : ProofBudget h s b) (hab : a ≤ b) :
    ProofBudget h s a := fun size hsz t c hr hca => hp size hsz t c hr (Nat.le_trans hca hab)

/-- Within the budget, the VM's check after an operation passes. -/
theorem recordedStorageError_none {h : NearState} {s t : State} {a b : Nat} (hp : ProofBudget h s b)
    (hst : ProofStep s t a) (hab : a ≤ b) : recordedStorageError h t = none := by
  unfold recordedStorageError
  cases hs : h.storageProofSize with
  | none => rfl
  | some size =>
    simp only
    rw [if_neg (Nat.not_lt.mpr (hp size hs t (a + 0) (.step hst (.refl t)) (by omega)))]
/-! ## The storage phase -/

/-- The storage phase of `storage_read` over a canonical trie succeeds: it only moves
the accounting and burns at most `storageReadPhaseUse`, as `ext` charges. -/
theorem prepareStorageCallAux_read (before : HostStore NearState) (len ptr r : UInt64)
    (key rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before ptr len = some key)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : lookupProofBound rawKey ≤ b)
    (h1 : before.host.gas.used + storageReadPhaseUse before.host rawKey (before.host.storage key) ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ after s'', prepareStorageCallAux "storage_read" before [.i64 len, .i64 ptr, .i64 r] = (after, none) ∧
      after.host.storageAccounting = some s'' ∧ SameData s s'' ∧
      after.host.gas.burnt ≤
        before.host.gas.burnt + storageReadPhaseUse before.host rawKey (before.host.storage key) ∧
      after.host.gas.promises = before.host.gas.promises := by
  obtain ⟨s', p, hget, hsd, ⟨d, m, hd, hm, hdm⟩, hpres, hder⟩ :=
    storage_lookup_view (k := rawKey) before.host.storageReadsFromTrie hb hz
  have hcon : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "storage_read" = true := by decide
  have e1 : ("storage_read" == "storage_write") = false := by decide
  have e2 : ("storage_read" == "storage_remove") = false := by decide
  have e3 : ("storage_read" != "storage_has_key") = true := by decide
  have e4 : ("storage_read" == "storage_read") = true := by decide
  have hlk : ∀ l, before.host.config.maxStorageKeyLen = some l → ¬ key.length > l := by
    intro l hl; rw [hl] at hlim; simpa [withinLimit] using hlim
  have hdd : s'.accounting.disk - s.accounting.disk = d := by omega
  have hmm : s'.accounting.mem - s.accounting.mem = m := by omega
  rw [← hlink] at hpres hder
  simp only [prepareStorageCallAux, hcon, hacc, argU64, Id.run]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, hkey, e1, e2, e3, e4, Bool.false_or,
    Bool.or_false, ite_true, Bool.false_eq_true, ite_false]
  rw [← hraw, hget]
  have hext : ExtOnly (trieNodeCharges d m) := by
    intro c hc; simp only [trieNodeCharges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact ⟨_, _, rfl⟩
  have hph : (2 * rawKey.length + 1) * trieNodeMax before.host ≤
      storageReadPhaseUse before.host rawKey (before.host.storage key) := by
    unfold storageReadPhaseUse; omega
  split
  on_goal 1 => rename_i lim hml; rw [if_neg (hlk lim hml)]
  all_goals
    dsimp only
    rw [hdd, hmm]
    set ns0 : NearState := { before.host with storageAccounting := some s' } with hns0
    have htc : chargesUse ns0 (trieNodeCharges d m) ≤ (2 * rawKey.length + 1) * trieNodeMax before.host :=
      Nat.le_trans (trieNodeCharges_use ns0 d m) (Nat.mul_le_mul_right _ hdm)
    obtain ⟨ok1, ch1⟩ := applyCharges_ok ns0 (trieNodeCharges d m) (C := C) (by
      show before.host.gas.used + _ ≤ C; omega) h2 h3
    have pr1 := applyCharges_ext_promises ns0 (trieNodeCharges d m) hext (C := C) (by
      show before.host.gas.used + _ ≤ C; omega) h2 h3
    simp only [trieNodeCharges] at ok1 ch1 pr1 htc
    generalize hA : applyCharges ns0 [Charge.ext "touching_trie_node" d, Charge.ext "read_cached_trie_node" m] = A at ok1 ch1 pr1 ⊢
    obtain ⟨ns1, err1⟩ := A
    simp only at ok1 ch1 pr1
    subst ok1
    have hrec : recordedStorageError ns1 s' = none := by
      have ha : ns1.storageProofSize = before.host.storageProofSize :=
        erase_field ch1.erase NearState.storageProofSize fun _ => rfl
      exact recordedStorageError_none (hproof.congr ha ch1.config) (.lookup hget) hbud
    simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false,
      hrec]
    have hu1 : ns1.gas.used = before.host.gas.used +
        chargesUse ns0 [Charge.ext "touching_trie_node" d, Charge.ext "read_cached_trie_node" m] := ch1.used
    have hp1 : ns1.gas.promises = before.host.gas.promises := pr1
    have hsa1 : ns1.storageAccounting = some s' := erase_field ch1.erase NearState.storageAccounting fun _ => rfl
    have h1' := h1
    simp only [Near.GasCounter.used] at h1'
    rcases hv : before.host.storage key with _ | v
    · have hpn : p = none := by
        cases p with
        | none => rfl
        | some _ => rw [hv] at hpres; cases hpres
      subst hpn
      simp only [Option.isSome_none, bne_self_eq_false, Bool.false_eq_true, ite_false]
      refine ⟨_, s', rfl, hsa1, hsd, ?_, hp1⟩
      rw [hv] at hph h1'
      show ns1.gas.burnt ≤ _
      simp only [Near.GasCounter.used] at hu1
      omega
    · obtain ⟨q, s'', rfl, hq, hd2, hsd2⟩ := hder v hv
      simp only [Option.isSome_some, bne_self_eq_false, Bool.false_eq_true, ite_false, hq, refOf]
      rw [hd2]
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
      have hext2 : ExtOnly (storageReadValueCharges v.length) := by
        intro c hc
        simp only [storageReadValueCharges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | hc
        · exact ⟨_, _, rfl⟩
        · split at hc
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;> exact ⟨_, _, rfl⟩
          · simp at hc
      have hvu : chargesUse ns1 (storageReadValueCharges v.length) =
          chargesUse before.host (storageReadValueCharges v.length) :=
        chargesUse_of ch1.fees ch1.extCosts _
      have hph2 : (2 * rawKey.length + 1) * trieNodeMax before.host +
          chargesUse before.host (storageReadValueCharges v.length) =
          storageReadPhaseUse before.host rawKey (some v) := rfl
      rw [hv] at h1' hph
      simp only [Near.GasCounter.used] at hu1
      have hmb1 : ns1.gas.maxBurnt = before.host.gas.maxBurnt := ch1.maxBurnt
      have hpp1 : ns1.gas.prepaid = before.host.gas.prepaid := ch1.prepaid
      obtain ⟨ok2, ch2⟩ := applyCharges_ok ns1 (storageReadValueCharges v.length) (C := C)
        (by simp only [Near.GasCounter.used]; omega) (by omega) (by omega)
      have pr2 := applyCharges_ext_promises ns1 (storageReadValueCharges v.length) hext2 (C := C)
        (by simp only [Near.GasCounter.used]; omega) (by omega) (by omega)
      generalize hB : applyCharges ns1 (storageReadValueCharges v.length) = B at ok2 ch2 pr2 ⊢
      obtain ⟨ns2, err2⟩ := B
      simp only at ok2 ch2 pr2
      subst ok2
      have hu2 := ch2.used
      simp only [Near.GasCounter.used] at hu2
      simp only [Option.map_none, Option.isSome_none, bne_self_eq_false, Bool.false_eq_true, ite_false]
      refine ⟨_, s'', rfl, rfl, ?_, ?_, ?_⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hsd
        obtain ⟨b1, b2, b3, b4⟩ := hsd2
        exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩
      · show ns2.gas.burnt ≤ _
        omega
      · show ns2.gas.promises = _
        omega

/-! ## The metered call -/

/-- The charges of `storage_read` before it runs, for a key of `n` bytes in memory. -/
def storageReadBeforeCharges (n : Nat) : List Charge :=
  [.ext "base", .ext "storage_read_base", .ext "read_memory_base", .ext "read_memory_byte" n,
    .ext "storage_read_key_byte" n]

theorem chargesBefore_storageRead (st : HostStore NearState) (len ptr r : UInt64) (hlen : len ≠ u64Max) :
    chargesBefore "storage_read" st [.i64 len, .i64 ptr, .i64 r] = storageReadBeforeCharges len.toNat := by
  have hs : storageMutationPlan? "storage_read" st [.i64 len, .i64 ptr, .i64 r] = none := by
    simp [storageMutationPlan?]
  have hpre : "storage_read".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, readSpan, spanLen,
    hlen, storageReadBeforeCharges]

theorem preInvokeError_storageRead (st : HostStore NearState) (args : List Value) :
    preInvokeError "storage_read" st args = none := by
  simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
    creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
    functionCallInputError, functionCallInputs?]

/-- Post-call metering of `storage_read`: the after-charges, when they succeed. -/
theorem finish_storageRead (extra : Nat) (before st : HostStore NearState) (args vals : List Value)
    (h : (applyCharges st.host (chargesAfter "storage_read" before st args)).2 = none) :
    finishMeteredCall extra "storage_read" before args (.Return vals st) =
      .Return vals { st with host := (applyCharges st.host (chargesAfter "storage_read" before st args)).1 } := by
  simp only [finishMeteredCall]
  generalize applyCharges st.host (chargesAfter "storage_read" before st args) = A at h ⊢
  obtain ⟨ns, e⟩ := A
  simp only at h
  subst h
  simp (config := { decide := true }) [deductDeposit, promiseDeposit?, actionMethodEncodingError,
    actionMethodBytes?, functionCallInputs?, updateStorageUsage]

theorem chargesAfter_storageRead (before st : HostStore NearState) (len ptr r : UInt64) (key : List UInt8)
    (hkey : getMemOrReg before ptr len = some key) (hacc : before.host.storageAccounting.isSome = true) :
    chargesAfter "storage_read" before st [.i64 len, .i64 ptr, .i64 r] =
      ((before.host.storage key).map fun v => writeReg v.length).getD [] := by
  simp only [chargesAfter, argU64, List.getElem?_cons_succ, List.getElem?_cons_zero, hkey]
  cases before.host.storage key with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    cases h : before.host.storageAccounting with
    | none => rw [h] at hacc; cases hacc
    | some _ => simp

/-- The host after the storage phase: new accounting, burnt gas and gas profile. -/
def phaseHost (h : NearState) (s2 : State) (b : Nat) (p : Near.GasProfile) : NearState :=
  { h with storageAccounting := some s2, gas := { h.gas with burnt := b }, gasProfile := p }

/-- The storage phase of `storage_read`, as the metered wrapper sees it: only the
accounting (same data), the burnt gas (within `storageReadPhaseUse`) and the
gas profile change. -/
theorem prepareStorageCall_read (before : HostStore NearState) (len ptr r : UInt64)
    (key rawKey : List UInt8) (s : State) {C b : Nat}
    (hraw : rawKey = contractKey before.host.context.currentAccountId key)
    (hacc : before.host.storageAccounting = some s)
    (hkey : getMemOrReg before ptr len = some key)
    (hlim : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : before.host.storage key = viewVal s rawKey)
    (hproof : ProofBudget before.host s b) (hbud : lookupProofBound rawKey ≤ b)
    (h1 : before.host.gas.used + storageReadPhaseUse before.host rawKey (before.host.storage key) ≤ C)
    (h2 : C ≤ before.host.gas.maxBurnt) (h3 : C ≤ before.host.gas.prepaid) :
    ∃ s2 b p, prepareStorageCall "storage_read" before [.i64 len, .i64 ptr, .i64 r] =
        ({ before with host := phaseHost before.host s2 b p }, none) ∧ SameData s s2 ∧
      b ≤ before.host.gas.burnt + storageReadPhaseUse before.host rawKey (before.host.storage key) := by
  obtain ⟨after, s2, haux, hsa, hsd, hb', -⟩ :=
    prepareStorageCallAux_read before len ptr r key rawKey s hraw hacc hkey hlim hb hz hlink hproof hbud
      h1 h2 h3
  refine ⟨s2, after.host.gas.burnt, after.host.gasProfile, ?_, hsd, hb'⟩
  simp only [prepareStorageCall, haux, hsa, Option.isNone_none, ite_true, phaseHost]

/-! ## The contract -/

/-- What `storage_read` returns: `1` when the key has a value, `0` otherwise. -/
def storageReadResult (val : Option (List UInt8)) : List Value :=
  match val with
  | some _ => [.i64 1]
  | none => [.i64 0]

/-- The register update of `storage_read`: register `r` gets the value, when
there is one (nothing happens for the sentinel register `u64Max`). -/
def storageReadRegs (h : NearState) (r : UInt64) (val : Option (List UInt8)) : NearState :=
  match val with
  | some v => if r = u64Max then h else h.setRegister r.toNat v
  | none => h

@[simp] theorem storageReadRegs_gas (h : NearState) (r : UInt64) (val : Option (List UInt8)) :
    (storageReadRegs h r val).gas = h.gas := by
  unfold storageReadRegs; split
  · split <;> rfl
  · rfl

theorem storageReadRegs_fees (h : NearState) (r : UInt64) (val : Option (List UInt8)) :
    (storageReadRegs h r val).fees = h.fees ∧ (storageReadRegs h r val).extCosts = h.extCosts := by
  unfold storageReadRegs; split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem erase_storageReadRegs (h : NearState) (r : UInt64) (val : Option (List UInt8)) :
    erase (storageReadRegs h r val) = storageReadRegs (erase h) r val := by
  unfold storageReadRegs; split
  · split <;> rfl
  · rfl

/-- `storage_read` itself, after the metering: the result and the register. -/
theorem storageReadFn_invoke (st : HostStore NearState) (len ptr r : UInt64) (key : List UInt8)
    (hkey : getMemOrReg st ptr len = some key)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hreg : ∀ v, st.host.storage key = some v → r ≠ u64Max →
      withinLimit st.host.config.maxRegisterLen v.length = true) :
    storageReadFn.invoke st [.i64 len, .i64 ptr, .i64 r] =
      .Return (storageReadResult (st.host.storage key))
        { st with host := storageReadRegs st.host r (st.host.storage key) } := by
  simp only [storageReadFn, hkey, checkDataLimit, hlim, ite_true]
  cases hv : st.host.storage key with
  | none => rfl
  | some v =>
    simp only [writeRegisterResult, checkedSetRegister?, storageReadResult, storageReadRegs]
    by_cases hr : r = u64Max
    · simp [hr]
    · simp [hr, hreg v hv hr]

/-- What `storage_read(key)` into register `r` leaves, up to gas, from `h` with
accounting `s`: the register set as `storageReadRegs`, the accounting replaced by
one with the same data (`SameData`), and nothing else changed. -/
def StorageReadPost (h : NearState) (key : List UInt8) (r : UInt64) (s : State) (host' : NearState) : Prop :=
  ∃ s2, SameData s s2 ∧
    erase host' = erase (storageReadRegs { h with storageAccounting := some s2 } r (h.storage key))

/-- The gas `storage_read` of an `n`-byte key may use: the charges before, the
storage phase (`storageReadPhaseUse`), and writing the register. -/
def storageReadUse (h : NearState) (key : List UInt8) (n : Nat) : Nat :=
  chargesUse h (storageReadBeforeCharges n) +
    storageReadPhaseUse h (contractKey h.context.currentAccountId key) (h.storage key) +
    chargesUse h (((h.storage key).map fun v => writeReg v.length).getD [])

/-- The metered call on a store: the charges before, the storage phase, the host
function and the charges after all succeed within the credits. -/
theorem storageRead_ok (extra : Nat) (st : HostStore NearState) (len ptr r : UInt64) (key : List UInt8)
    (s : State) {C b : Nat} (hlen : len ≠ u64Max)
    (hkey : getMemOrReg st ptr len = some key)
    (hacc : st.host.storageAccounting = some s)
    (hlim : withinLimit st.host.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : st.host.storage key = viewVal s (contractKey st.host.context.currentAccountId key))
    (hproof : ProofBudget st.host s b)
    (hbud : lookupProofBound (contractKey st.host.context.currentAccountId key) ≤ b)
    (hreg : ∀ v, st.host.storage key = some v → r ≠ u64Max →
      withinLimit st.host.config.maxRegisterLen v.length = true)
    (h1 : st.host.gas.used + storageReadUse st.host key len.toNat ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "storage_read" storageReadFn).invoke st [.i64 len, .i64 ptr, .i64 r] =
        .Return (storageReadResult (st.host.storage key)) { mem := st.mem, host := host' } ∧
      StorageReadPost st.host key r s host' ∧
      host'.gas.used ≤ st.host.gas.used + storageReadUse st.host key len.toNat ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  have hdep : deprecatedRuntimeHost "storage_read" = false := by decide
  have hview : viewRestrictedHost "storage_read" = false := by decide
  have hu := h1
  unfold storageReadUse at hu
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (storageReadBeforeCharges len.toNat) (C := C) (by omega) h2 h3
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [chargesBefore_storageRead st len ptr r hlen]
  generalize hac : applyCharges st.host (storageReadBeforeCharges len.toNat) = ac at hok hch
  obtain ⟨ns, err⟩ := ac
  simp only at hok hch
  subst hok
  simp only
  rw [preInvokeError_storageRead]
  simp only
  show ∃ host', invokeStorageCall extra "storage_read" storageReadFn
    { mem := st.mem, host := afterCharges ns } [.i64 len, .i64 ptr, .i64 r] = _ ∧ _
  have he1 : erase (afterCharges ns) = erase st.host := by rw [erase_afterCharges, hch.erase]
  have fsa : (afterCharges ns).storageAccounting = st.host.storageAccounting :=
    erase_field he1 NearState.storageAccounting fun _ => rfl
  have fid : (afterCharges ns).context.currentAccountId = st.host.context.currentAccountId :=
    erase_field he1 (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have fcfg : (afterCharges ns).config = st.host.config := erase_field he1 NearState.config fun _ => rfl
  have fsto : (afterCharges ns).storage = st.host.storage := erase_field he1 NearState.storage fun _ => rfl
  have fpsz : (afterCharges ns).storageProofSize = st.host.storageProofSize :=
    erase_field he1 NearState.storageProofSize fun _ => rfl
  have ffee : (afterCharges ns).fees = st.host.fees := erase_field he1 NearState.fees fun _ => rfl
  have fext : (afterCharges ns).extCosts = st.host.extCosts := erase_field he1 NearState.extCosts fun _ => rfl
  have hgas1 : (afterCharges ns).gas = ns.gas := rfl
  have hkey1 : getMemOrReg { mem := st.mem, host := afterCharges ns } ptr len = some key := by
    exact (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := afterCharges ns }) hlen rfl).trans hkey
  have hphase : storageReadPhaseUse (afterCharges ns) (contractKey st.host.context.currentAccountId key)
      ((afterCharges ns).storage key) =
      storageReadPhaseUse st.host (contractKey st.host.context.currentAccountId key) (st.host.storage key) := by
    simp only [storageReadPhaseUse, trieNodeMax, fext, fsto]
    cases st.host.storage key <;> simp [chargesUse_of ffee fext]
  obtain ⟨s2, b, p, hpre, hsd, hbb⟩ := prepareStorageCall_read { mem := st.mem, host := afterCharges ns }
    len ptr r key (contractKey st.host.context.currentAccountId key) s (C := C) (by rw [fid])
    (by rw [fsa]; exact hacc) hkey1 (by rw [fcfg]; exact hlim) hb hz
    (by rw [fsto]; exact hlink) (hproof.congr fpsz fcfg) hbud
    (by rw [hphase, hgas1, hch.used]; omega) (by rw [hgas1, hch.maxBurnt]; exact h2)
    (by rw [hgas1, hch.prepaid]; exact h3)
  rw [hphase] at hbb
  simp only [invokeStorageCall, hpre]
  set H2 := phaseHost (afterCharges ns) s2 b p with hH2
  have hkey2 : getMemOrReg { mem := st.mem, host := H2 } ptr len = some key :=
    (getMemOrReg_mem (s := st) (s' := { mem := st.mem, host := H2 }) hlen rfl).trans hkey
  have hsto2 : H2.storage = st.host.storage := fsto
  have hcfg2 : H2.config = st.host.config := fcfg
  rw [storageReadFn_invoke { mem := st.mem, host := H2 } len ptr r key hkey2 (by rw [hcfg2]; exact hlim)
    (by rw [hcfg2, hsto2]; exact hreg)]
  rw [hsto2]
  set H3 := storageReadRegs H2 r (st.host.storage key) with hH3
  have hca := chargesAfter_storageRead { mem := st.mem, host := H2 }
    { mem := st.mem, host := H3 } len ptr r key hkey2 (by
      show (phaseHost _ _ _ _).storageAccounting.isSome = true; rfl)
  simp only [hsto2] at hca
  set cs := ((st.host.storage key).map fun v => writeReg v.length).getD [] with hcs
  have hfe3 := storageReadRegs_fees H2 r (st.host.storage key)
  have hcu : chargesUse H3 cs = chargesUse st.host cs := by
    exact chargesUse_of (hfe3.1.trans ffee) (hfe3.2.trans fext) cs
  have hg3 : H3.gas = { ns.gas with burnt := b } := by rw [hH3, storageReadRegs_gas]; rfl
  have hn := hch.used
  have hbb' : b ≤ ns.gas.burnt + storageReadPhaseUse st.host (contractKey st.host.context.currentAccountId key) (st.host.storage key) := hbb
  simp only [Near.GasCounter.used] at hn hu
  obtain ⟨ok4, ch4⟩ := applyCharges_ok H3 cs (C := C)
    (by rw [hcu, hg3]; simp only [Near.GasCounter.used]; omega)
    (by rw [hg3]; show C ≤ ns.gas.maxBurnt; rw [hch.maxBurnt]; exact h2)
    (by rw [hg3]; show C ≤ ns.gas.prepaid; rw [hch.prepaid]; exact h3)
  rw [finish_storageRead extra _ _ _ _ (by rw [hca]; exact ok4), hca]
  refine ⟨(applyCharges H3 cs).1, rfl, ⟨s2, hsd, ?_⟩, ?_, ?_, ?_⟩
  · rw [ch4.erase, hH3, erase_storageReadRegs, erase_storageReadRegs]
    show storageReadRegs { erase (afterCharges ns) with storageAccounting := some s2 } r _ = _
    rw [he1]; rfl
  · rw [ch4.used, hcu, hg3]
    show _ ≤ st.host.gas.used + (_ + _ + chargesUse st.host cs)
    simp only [Near.GasCounter.used]
    omega
  · rw [ch4.maxBurnt, hg3]; exact hch.maxBurnt
  · rw [ch4.prepaid, hg3]; exact hch.prepaid

theorem storageReadUse_erase {h h' : NearState} (he : erase h = erase h') (key : List UInt8) (n : Nat) :
    storageReadUse h key n = storageReadUse h' key n := by
  have hf : h.fees = h'.fees := erase_field he NearState.fees fun _ => rfl
  have hx : h.extCosts = h'.extCosts := erase_field he NearState.extCosts fun _ => rfl
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  have hi : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  unfold storageReadUse storageReadPhaseUse trieNodeMax
  rw [hs, hi, hx, chargesUse_of hf hx, chargesUse_of hf hx]
  cases h'.storage key <;> simp [chargesUse_of hf hx]

theorem erase_withAcc (x : NearState) (a : Option State) :
    erase { x with storageAccounting := a } = { erase x with storageAccounting := a } := rfl

theorem storageReadPost_erase {h h' host' : NearState} (he : erase h = erase h') {key : List UInt8}
    {r : UInt64} {s : State} (hq : StorageReadPost h key r s host') : StorageReadPost h' key r s host' := by
  obtain ⟨s2, hsd, hq⟩ := hq
  have hs : h.storage = h'.storage := erase_field he NearState.storage fun _ => rfl
  refine ⟨s2, hsd, ?_⟩
  have hw : erase { h with storageAccounting := some s2 } = erase { h' with storageAccounting := some s2 } := by
    show { erase h with storageAccounting := some s2 } = { erase h' with storageAccounting := some s2 }
    rw [he]
  rw [hq, erase_storageReadRegs, erase_storageReadRegs, hw, hs]

/-- **`storage_read`, metered**, as a read contract: with the key's `len` bytes
`key` at `ptr`, over a host whose storage accounting `s` is a canonical trie
linked to its `storage` (`hlink`), the call returns `1` (and sets register `r`
to the value) or `0`, leaves the host as `StorageReadPost`, and uses at most
`storageReadUse` gas. -/
theorem storageRead_readContract (extra : Nat) (h : NearState) (len ptr r : UInt64) (key : List UInt8)
    (s : State) {C b : Nat} (hlen : len ≠ u64Max) (hkl : key.length = len.toNat) (hpos : 0 < len.toNat)
    (hacc : h.storageAccounting = some s)
    (hlim : withinLimit h.config.maxStorageKeyLen key.length = true)
    (hb : build s.entries = .ok s.base) (hz : zeroHash ∉ s.base.witness.map Prod.fst)
    (hlink : h.storage key = viewVal s (contractKey h.context.currentAccountId key))
    (hproof : ProofBudget h s b) (hbud : lookupProofBound (contractKey h.context.currentAccountId key) ≤ b)
    (hreg : ∀ v, h.storage key = some v → r ≠ u64Max → withinLimit h.config.maxRegisterLen v.length = true) :
    ReadContractP (metered extra "storage_read" storageReadFn).toHostFn h (StorageReadPost h key r s)
      [.i64 len, .i64 ptr, .i64 r] (storageReadResult (h.storage key)) ptr.toNat key
      (storageReadUse h key len.toNat) C := by
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
  rw [← storageReadUse_erase he] at hu ⊢
  obtain ⟨host', hinv, hq, hused, hmb', hpp'⟩ := storageRead_ok extra { mem, host } len ptr r key s (C := C)
    hlen hkey (by rw [fsa]; exact hacc) (by rw [fcfg]; exact hlim) hb hz
    (by rw [fsto, fid]; exact hlink)
    (hproof.congr fpsz fcfg) (by rw [fid]; exact hbud)
    (by rw [fsto, fcfg]; exact hreg) hu hmb hpp
  refine ⟨host', ?_, storageReadPost_erase he hq, hused, hmb', hpp'⟩
  simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
  rw [show host.storage key = h.storage key by rw [fsto]]

end NearLogic
