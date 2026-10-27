import NearVM.MeteredHosts.Storage
import NearVM.MeteredHosts.Charges
import NearVM.MeteredHosts.Output
import NearVM.GasInvariants

/-!
# Metered storage-write contract

The external trie phase is exposed through individual reference lookup,
dereference, accounting charges and proof-size checks. These are local
obligations about the trie primitives, not a postcondition for the complete
host invocation. The wrapper contract then composes that phase with the raw
write, post-call charges and storage-usage update.
-/

namespace Wasm.Near.MeteredHosts.StorageMetered

/-- The M2 call discards the evicted-value output register. -/
def args (keyLen keyPtr valueLen valuePtr : UInt64) : List Value :=
  [.i64 keyLen, .i64 keyPtr, .i64 valueLen, .i64 valuePtr, .i64 u64Max]

/-- Trie lookup and dereference are billed against the phase's initial
accounting snapshot, preserving cache warming between the two operations. -/
def trieCharges (initial final : _root_.Near.TrieOverlay.State) : List Charge :=
  [.ext "touching_trie_node" (final.accounting.disk - initial.accounting.disk),
    .ext "read_cached_trie_node" (final.accounting.mem - initial.accounting.mem)]

def accounted (before : HostStore NearState) (trie : _root_.Near.TrieOverlay.State) : HostStore NearState :=
  { before with host := { before.host with storageAccounting := some trie } }

/-- `prepareStorageCall` exposes only trie accounting and burnt gas/profile;
its successful splice retains the caller's promise reservations and limits. -/
def prepared (before : HostStore NearState) (paid : NearState)
    (trie : _root_.Near.TrieOverlay.State) : HostStore NearState :=
  { before with host := { before.host with
    storageAccounting := some trie,
    gas := { before.host.gas with burnt := paid.gas.burnt },
    gasProfile := paid.gasProfile } }

-- The runtime currently keeps this implementation helper private. The local
-- tactic unfolds that transparent declaration by its kernel name; the proof
-- still checks against the actual public `prepareStorageCall` definition.
local macro "unfold_storage_aux" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearVM.Metered 0) "Wasm") "Near") "prepareStorageCallAux"
  `(tactic| unfold $(Lean.mkIdent name))

set_option maxHeartbeats 1500000 in
/-- Fresh-key trie phase. Its obligations expose exactly the lookup, billed
node totals, and final storage-proof check; no dereference is necessary. -/
theorem prepare_fresh (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (initial looked : _root_.Near.TrieOverlay.State) (paid : NearState)
    (haccounting : before.host.storageAccounting = some initial)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) true = .ok (looked, none))
    (hstorage : before.host.storage key = none)
    (hcharge : applyCharges (accounted before looked).host (trieCharges initial looked) = (paid, none))
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hproof : recordedStorageError paid
      (looked.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value) = none) :
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) =
      (prepared before paid
        (looked.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value), none) := by
  simp only [accounted, trieCharges] at hcharge
  simp only [recordedStorageError] at hproof
  unfold prepareStorageCall
  unfold_storage_aux
  simp only [Id.run, pure, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_write" = true by decide,
    ↓reduceIte, haccounting, hkey]
  cases hlimit : before.host.config.maxStorageKeyLen with
  | none =>
      simp [hlookup, hstorage, hvalue, hcharge, recordedStorageError, hproof, prepared]
  | some limit =>
      simp only [Nat.not_lt_of_ge (hkeyLimit limit hlimit), ↓reduceIte]
      simp [hlookup, hstorage, hvalue, hcharge, recordedStorageError, hproof, prepared]

set_option maxHeartbeats 1500000 in
/-- Replacement trie phase: old-value bytes are paid before dereference;
lookup/dereference node deltas are paid before staging the new value. -/
theorem prepare_replace (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value old : List UInt8)
    (initial looked fetched : _root_.Near.TrieOverlay.State)
    (pointer : _root_.Near.TrieOverlay.ValuePointer) (valuePaid nodePaid : NearState)
    (haccounting : before.host.storageAccounting = some initial)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) true = .ok (looked, some pointer))
    (hstorage : before.host.storage key = some old)
    (hvalueCharge : applyCharges (accounted before looked).host
      [.ext "storage_write_evicted_byte" pointer.reference.2.length] = (valuePaid, none))
    (hfetch : _root_.Near.TrieOverlay.dereference looked pointer = .ok (fetched, old))
    (hnodeCharge : applyCharges { valuePaid with storageAccounting := some fetched }
      (trieCharges initial fetched) = (nodePaid, none))
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hproof : recordedStorageError nodePaid
      (fetched.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value) = none) :
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) =
      (prepared before nodePaid
        (fetched.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value), none) := by
  simp only [accounted] at hvalueCharge
  simp only [trieCharges] at hnodeCharge
  simp only [recordedStorageError] at hproof
  unfold prepareStorageCall
  unfold_storage_aux
  simp only [Id.run, pure, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ,
    show ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "storage_write" = true by decide,
    ↓reduceIte, haccounting, hkey]
  cases hlimit : before.host.config.maxStorageKeyLen with
  | none =>
      simp [hlookup, hstorage, hvalueCharge, hfetch, hnodeCharge, hvalue,
        recordedStorageError, hproof, prepared]
  | some limit =>
      simp only [Nat.not_lt_of_ge (hkeyLimit limit hlimit), ↓reduceIte]
      simp [hlookup, hstorage, hvalueCharge, hfetch, hnodeCharge, hvalue,
        recordedStorageError, hproof, prepared]

/-- Post-invocation register cost, including replacement when the output
register is the discard sentinel: this is what the current runtime charges. -/
def postCharges (before : HostStore NearState) (key : List UInt8) : List Charge :=
  match before.host.storage key with
  | none => []
  | some old => writeReg old.length

theorem postCharges_eq (before after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key : List UInt8)
    (hkey : getMemOrReg before keyPtr keyLen = some key) :
    chargesAfter "storage_write" before after (args keyLen keyPtr valueLen valuePtr) = postCharges before key := by
  simp only [chargesAfter, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ, hkey, postCharges]
  cases before.host.storage key <;> rfl

theorem postCharges_burnsOnly (before : HostStore NearState) (key : List UInt8) :
    ∀ charge ∈ postCharges before key, BurnsOnly charge := by
  cases h : before.host.storage key <;> simp [postCharges, h, writeReg, BurnsOnly]

/-- The successful finish performs exactly the post-call billing and usage
update. No promise deposit or method-encoding check affects storage writes. -/
theorem finish_discard (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (postPaid : NearState)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hcharge : applyCharges (written before key value).host (postCharges before key) = (postPaid, none)) :
    finishMeteredCall extra "storage_write" before (args keyLen keyPtr valueLen valuePtr)
      (.Return [.i64 (if (before.host.storage key).isSome then 1 else 0)] (written before key value)) =
      .Return [.i64 (if (before.host.storage key).isSome then 1 else 0)]
        (updateStorageUsage extra "storage_write" before
          { written before key value with host := postPaid } (args keyLen keyPtr valueLen valuePtr)) := by
  simp only [finishMeteredCall]
  rw [postCharges_eq _ _ _ _ _ _ _ hkey, hcharge]
  simp [deductDeposit, promiseDeposit?, actionMethodEncodingError, actionMethodBytes?,
    usesKeyMethodFields, functionCallInputs?]

/-- Input validation for the storage write, independently of its gas plan. -/
theorem preInvoke_ok (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hkeyLimit : withinLimit before.host.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit before.host.config.maxStorageValueLen value.length = true) :
    preInvokeError "storage_write" before (args keyLen keyPtr valueLen valuePtr) = none := by
  have herr : (storageMutationPlan? "storage_write" before
      (args keyLen keyPtr valueLen valuePtr)).map (·.error) = some none := by
    simp only [storageMutationPlan?, args, argU64, List.getElem?_cons_zero,
      List.getElem?_cons_succ, hkey, hvalue]
    cases hk : before.host.config.maxStorageKeyLen <;>
      cases hv : before.host.config.maxStorageValueLen <;>
      simp_all [withinLimit]
    all_goals repeat' (first | (split <;> simp_all) | omega)
  cases hplan : storageMutationPlan? "storage_write" before (args keyLen keyPtr valueLen valuePtr) with
  | none => simp [hplan] at herr
  | some plan =>
      have hp : plan.error = none := by simpa only [hplan, Option.map_some, Option.some.injEq] using herr
      simp only [preInvokeError, invocationArgumentError, hplan, hp]
      rfl

/-- Composition at the real metered wrapper. The trie phase is a local
contract, discharged by `prepare_fresh` or `prepare_replace`; the two charge
premises are the actual pre- and post-call billings. -/
theorem metered_discard (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (prePaid phasePaid postPaid : NearState) (trie : _root_.Near.TrieOverlay.State)
    (hview : before.host.context.isView = false)
    (hpre : applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr)) = (prePaid, none))
    (hpaidView : prePaid.context.isView = false)
    (hkey : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hvalue : getMemOrReg (Output.paidStore before prePaid) valuePtr valueLen = some value)
    (hkeyLimit : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit prePaid.config.maxStorageValueLen value.length = true)
    (hphase : prepareStorageCall "storage_write" (Output.paidStore before prePaid)
      (args keyLen keyPtr valueLen valuePtr) =
      (prepared (Output.paidStore before prePaid) phasePaid trie, none))
    (hpost : applyCharges
      (written (prepared (Output.paidStore before prePaid) phasePaid trie) key value).host
      (postCharges (prepared (Output.paidStore before prePaid) phasePaid trie) key) = (postPaid, none)) :
    (metered extra "storage_write" storageWriteFn).invoke before
      (args keyLen keyPtr valueLen valuePtr) =
      .Return [.i64 (if (prePaid.storage key).isSome then 1 else 0)]
        (updateStorageUsage extra "storage_write"
          (prepared (Output.paidStore before prePaid) phasePaid trie)
          { written (prepared (Output.paidStore before prePaid) phasePaid trie) key value with host := postPaid }
          (args keyLen keyPtr valueLen valuePtr)) := by
  have hp := preInvoke_ok (Output.paidStore before prePaid) keyLen keyPtr valueLen valuePtr key value
    hkey hvalue hkeyLimit hvalueLimit
  simp only [metered, show deprecatedRuntimeHost "storage_write" = false by decide,
    hview, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hpre]
  change (match preInvokeError "storage_write" (Output.paidStore before prePaid)
    (args keyLen keyPtr valueLen valuePtr) with
    | some error => trapWith (Output.paidStore before prePaid) error
    | none => invokeStorageCall extra "storage_write" storageWriteFn (Output.paidStore before prePaid)
      (args keyLen keyPtr valueLen valuePtr)) = _
  rw [hp]
  simp only [invokeStorageCall, hphase]
  simp only [args]
  rw [storageWrite_discard (prepared (Output.paidStore before prePaid) phasePaid trie)
    keyLen keyPtr valueLen valuePtr key value hpaidView hkey hvalue hkeyLimit hvalueLimit]
  exact finish_discard extra (prepared (Output.paidStore before prePaid) phasePaid trie)
    keyLen keyPtr valueLen valuePtr key value postPaid hkey hpost

/-- Every trie-accounting charge is a burn, so reservations are framed. -/
theorem trieCharges_burnsOnly (initial final : _root_.Near.TrieOverlay.State) :
    ∀ charge ∈ trieCharges initial final, BurnsOnly charge := by
  simp [trieCharges, BurnsOnly]

/-- A successful phase's splice agrees with its paid gas counter when its
promise reservations and limits are unchanged. -/
theorem prepared_gas_eq (before : HostStore NearState) (paid : NearState)
    (trie : _root_.Near.TrieOverlay.State)
    (hpromises : paid.gas.promises = before.host.gas.promises)
    (hprepaid : paid.gas.prepaid = before.host.gas.prepaid)
    (hlimit : paid.gas.maxBurnt = before.host.gas.maxBurnt) :
    (prepared before paid trie).host.gas = paid.gas := by
  cases hb : before.host.gas
  cases hp : paid.gas
  simp_all [prepared]

/-- The recorded-proof check depends only on functional fields preserved by
burn charges, not on their gas/profile mutations. -/
theorem recordedStorageError_charges (before : HostStore NearState) (charges : List Charge)
    (trie : _root_.Near.TrieOverlay.State) (hburn : ∀ charge ∈ charges, BurnsOnly charge) :
    recordedStorageError (applyCharges before.host charges).1 trie =
      recordedStorageError before.host trie := by
  have hfr := applyCharges_frame before.host charges hburn
  have hcfg := congrArg NearState.config hfr
  have hsize := congrArg NearState.storageProofSize hfr
  simp only at hcfg hsize
  simp only [recordedStorageError, hsize, hcfg]

/-- The fresh-key phase with credits: node-accounting bills are discharged,
with exact cost and residual credits on the actual prepared store. -/
theorem prepare_fresh_credits (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (initial looked : _root_.Near.TrieOverlay.State) (rest : Nat)
    (haccounting : before.host.storageAccounting = some initial)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) true = .ok (looked, none))
    (hstorage : before.host.storage key = none)
    (hcredits : before.host.gas.Credits (burnSum before.host.extCosts (trieCharges initial looked) + rest))
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hproof : recordedStorageError before.host
      (looked.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value) = none) :
    let paid := (applyCharges (accounted before looked).host (trieCharges initial looked)).1
    let result := prepared before paid
      (looked.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value)
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) = (result, none) ∧
      result.host.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (trieCharges initial looked) ∧
      result.host.gas.Credits rest := by
  let charges := trieCharges initial looked
  let paid := (applyCharges (accounted before looked).host charges).1
  have hc := applyCharges_credits (accounted before looked).host charges rest
    (trieCharges_burnsOnly initial looked) hcredits
  have hgas := applyCharges_gas_limits (accounted before looked).host charges
  have heq := prepared_gas_eq before paid
    (looked.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value)
    hc.2.2.1 hgas.1 hgas.2
  refine ⟨prepare_fresh before keyLen keyPtr valueLen valuePtr key value initial looked paid
    haccounting hkey hkeyLimit hlookup hstorage (Prod.ext rfl hc.1) hvalue ?_, ?_, ?_⟩
  · rw [recordedStorageError_charges (accounted before looked) charges _
      (trieCharges_burnsOnly initial looked)]
    exact hproof
  · exact hc.2.1
  · rw [heq]
    exact hc.2.2.2.2

/-- The byte bill for an old-value reference precedes dereference, including
when the caller discards the evicted-value register. -/
def evictedCharges (pointer : _root_.Near.TrieOverlay.ValuePointer) : List Charge :=
  [.ext "storage_write_evicted_byte" pointer.reference.2.length]

theorem evictedCharges_burnsOnly (pointer : _root_.Near.TrieOverlay.ValuePointer) :
    ∀ charge ∈ evictedCharges pointer, BurnsOnly charge := by
  simp [evictedCharges, BurnsOnly]

/-- Replacement phase with credits for old-value bytes and the combined
lookup/dereference node delta, in the runtime's actual charge order. -/
theorem prepare_replace_credits (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value old : List UInt8)
    (initial looked fetched : _root_.Near.TrieOverlay.State)
    (pointer : _root_.Near.TrieOverlay.ValuePointer) (rest : Nat)
    (haccounting : before.host.storageAccounting = some initial)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hlookup : _root_.Near.TrieOverlay.getReference initial
      (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) true = .ok (looked, some pointer))
    (hstorage : before.host.storage key = some old)
    (hfetch : _root_.Near.TrieOverlay.dereference looked pointer = .ok (fetched, old))
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (evictedCharges pointer) +
        (burnSum before.host.extCosts (trieCharges initial fetched) + rest)))
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hproof : recordedStorageError before.host
      (fetched.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value) = none) :
    let valuePaid := (applyCharges (accounted before looked).host (evictedCharges pointer)).1
    let mid := accounted { before with host := valuePaid } fetched
    let nodePaid := (applyCharges mid.host (trieCharges initial fetched)).1
    let result := prepared before nodePaid
      (fetched.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value)
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) = (result, none) ∧
      result.host.gas.burnt = before.host.gas.burnt +
        (burnSum before.host.extCosts (evictedCharges pointer) +
          burnSum before.host.extCosts (trieCharges initial fetched)) ∧
      result.host.gas.Credits rest := by
  let valuePaid := (applyCharges (accounted before looked).host (evictedCharges pointer)).1
  let mid := accounted { before with host := valuePaid } fetched
  let nodePaid := (applyCharges mid.host (trieCharges initial fetched)).1
  have hfirst := applyCharges_credits (accounted before looked).host (evictedCharges pointer)
    (burnSum before.host.extCosts (trieCharges initial fetched) + rest)
    (evictedCharges_burnsOnly pointer) hcredits
  have hsecond := applyCharges_credits mid.host (trieCharges initial fetched) rest
    (trieCharges_burnsOnly initial fetched)
    (by
      change valuePaid.gas.Credits (burnSum valuePaid.extCosts (trieCharges initial fetched) + rest)
      rw [show valuePaid.extCosts = before.host.extCosts from hfirst.2.2.2.1]
      exact hfirst.2.2.2.2)
  have hl1 := applyCharges_gas_limits (accounted before looked).host (evictedCharges pointer)
  have hl2 := applyCharges_gas_limits mid.host (trieCharges initial fetched)
  have heq := prepared_gas_eq before nodePaid
    (fetched.set (_root_.Near.TrieOverlay.contractKey before.host.context.currentAccountId key) value)
    (hsecond.2.2.1.trans hfirst.2.2.1) (hl2.1.trans hl1.1) (hl2.2.trans hl1.2)
  refine ⟨prepare_replace before keyLen keyPtr valueLen valuePtr key value old initial looked fetched pointer
    valuePaid nodePaid haccounting hkey hkeyLimit hlookup hstorage (Prod.ext rfl hfirst.1) hfetch
    (Prod.ext rfl hsecond.1) hvalue ?_, ?_, ?_⟩
  · rw [recordedStorageError_charges mid (trieCharges initial fetched) _
      (trieCharges_burnsOnly initial fetched)]
    change recordedStorageError valuePaid _ = none
    rw [recordedStorageError_charges (accounted before looked) (evictedCharges pointer) _
      (evictedCharges_burnsOnly pointer)]
    exact hproof
  · change nodePaid.gas.burnt = _
    have hcost2 : nodePaid.gas.burnt = valuePaid.gas.burnt +
        burnSum valuePaid.extCosts (trieCharges initial fetched) := hsecond.2.1
    have hcost1 : valuePaid.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (evictedCharges pointer) := hfirst.2.1
    rw [hcost2, show valuePaid.extCosts = before.host.extCosts from hfirst.2.2.2.1, hcost1]
    exact Nat.add_assoc _ _ _
  · rw [heq]
    exact hsecond.2.2.2.2

/-- Complete store after successful post-call billing and usage accounting. -/
def finished (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (paid : NearState) :
    HostStore NearState :=
  updateStorageUsage extra "storage_write" before { written before key value with host := paid }
    (args keyLen keyPtr valueLen valuePtr)

theorem finished_gas (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (paid : NearState) :
    (finished extra before keyLen keyPtr valueLen valuePtr key value paid).host.gas = paid.gas := by
  simp only [finished, updateStorageUsage]
  split <;> rfl

/-- After the actual post-call charge, the model usage is computed from the
original cell and new value, with ABI wrapping explicit. -/
theorem finished_usage (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (paid : NearState)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hcharge : applyCharges (written before key value).host (postCharges before key) = (paid, none)) :
    (finished extra before keyLen keyPtr valueLen valuePtr key value paid).host.context.storageUsage =
      UInt64.ofNat (writeUsage extra before key value) := by
  have hf := applyCharges_frame (written before key value).host (postCharges before key)
    (postCharges_burnsOnly before key)
  rw [hcharge] at hf
  have hcontext := congrArg NearState.context hf
  change paid.context = before.host.context at hcontext
  have hcell : paid.storage key = some value := by
    have hc := congrArg (fun ns : NearState => ns.storage key) hf
    exact hc.trans (written_here before key value)
  simp only [finished, updateStorageUsage, args, argU64, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hkey, hcontext, hcell, Option.map_some]
  cases hs : before.host.storage key <;> simp [writeUsage, hs]

/-- With the runtime's storage-usage room invariant, the usage agrees as a
natural number rather than only after conversion to the ABI word. -/
theorem finished_usage_toNat (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (paid : NearState)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hcharge : applyCharges (written before key value).host (postCharges before key) = (paid, none))
    (hroom : writeUsage extra before key value < 2 ^ 64) :
    (finished extra before keyLen keyPtr valueLen valuePtr key value paid).host.context.storageUsage.toNat =
      writeUsage extra before key value := by
  rw [finished_usage extra before keyLen keyPtr valueLen valuePtr key value paid hkey hcharge]
  exact UInt64.toNat_ofNat_of_lt' hroom

/-- Post-call credits pay the runtime's actual evicted-register cost and
retain the residual frame through the storage-usage update. -/
theorem finish_discard_credits (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (rest : Nat)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hcredits : before.host.gas.Credits (burnSum before.host.extCosts (postCharges before key) + rest)) :
    let paid := (applyCharges (written before key value).host (postCharges before key)).1
    let result := finished extra before keyLen keyPtr valueLen valuePtr key value paid
    finishMeteredCall extra "storage_write" before (args keyLen keyPtr valueLen valuePtr)
      (.Return [.i64 (if (before.host.storage key).isSome then 1 else 0)] (written before key value)) =
      .Return [.i64 (if (before.host.storage key).isSome then 1 else 0)] result ∧
      result.host.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts (postCharges before key) ∧
      result.host.gas.Credits rest ∧
      result.host.context.storageUsage = UInt64.ofNat (writeUsage extra before key value) := by
  have hc := applyCharges_credits (written before key value).host (postCharges before key) rest
    (postCharges_burnsOnly before key) hcredits
  have hcharge : applyCharges (written before key value).host (postCharges before key) =
      ((applyCharges (written before key value).host (postCharges before key)).1, none) :=
    Prod.ext rfl hc.1
  refine ⟨finish_discard extra before keyLen keyPtr valueLen valuePtr key value _ hkey hcharge, ?_, ?_,
    finished_usage extra before keyLen keyPtr valueLen valuePtr key value _ hkey hcharge⟩
  · rw [finished_gas]
    exact hc.2.1
  · rw [finished_gas]
    exact hc.2.2.2.2

/-- Actual metered storage-write contract after the pre-call payment and
trie-phase contract. The latter's credit result pays the post-call register
bill and leaves a caller-owned residual frame. The exact phase cost is given
by `prepare_fresh_credits` or `prepare_replace_credits`. -/
theorem metered_discard_credits (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8)
    (prePaid phasePaid : NearState) (trie : _root_.Near.TrieOverlay.State) (rest : Nat)
    (hview : before.host.context.isView = false)
    (hpre : applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr)) = (prePaid, none))
    (hpaidView : prePaid.context.isView = false)
    (hkey : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hvalue : getMemOrReg (Output.paidStore before prePaid) valuePtr valueLen = some value)
    (hkeyLimit : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit prePaid.config.maxStorageValueLen value.length = true)
    (hphase : prepareStorageCall "storage_write" (Output.paidStore before prePaid)
      (args keyLen keyPtr valueLen valuePtr) =
      (prepared (Output.paidStore before prePaid) phasePaid trie, none))
    (hcredits : (prepared (Output.paidStore before prePaid) phasePaid trie).host.gas.Credits
      (burnSum prePaid.extCosts (postCharges (prepared (Output.paidStore before prePaid) phasePaid trie) key) + rest)) :
    let phase := prepared (Output.paidStore before prePaid) phasePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    let result := finished extra phase keyLen keyPtr valueLen valuePtr key value paid
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Return [.i64 (if (prePaid.storage key).isSome then 1 else 0)] result ∧
      result.host.gas.burnt = phasePaid.gas.burnt + burnSum prePaid.extCosts (postCharges phase key) ∧
      result.host.gas.Credits rest ∧
      result.host.context.storageUsage = UInt64.ofNat (writeUsage extra phase key value) := by
  let phase := prepared (Output.paidStore before prePaid) phasePaid trie
  have hc := applyCharges_credits (written phase key value).host (postCharges phase key) rest
    (postCharges_burnsOnly phase key) hcredits
  refine ⟨metered_discard extra before keyLen keyPtr valueLen valuePtr key value prePaid phasePaid _ trie
    hview hpre hpaidView hkey hvalue hkeyLimit hvalueLimit hphase (Prod.ext rfl hc.1), ?_, ?_, ?_⟩
  · rw [finished_gas]
    exact hc.2.1
  · rw [finished_gas]
    exact hc.2.2.2.2
  · exact finished_usage extra phase keyLen keyPtr valueLen valuePtr key value _ hkey (Prod.ext rfl hc.1)

end Wasm.Near.MeteredHosts.StorageMetered
